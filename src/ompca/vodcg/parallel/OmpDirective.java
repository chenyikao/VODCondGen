/**
 * 
 */
package ompca.vodcg.parallel;

import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.NavigableSet;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorPragmaStatement;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.vodcg.ASTAddressable;
import ompca.vodcg.ASTRuntimeLocationComputer;
import ompca.vodcg.ASTUtil;
import ompca.vodcg.IncomparableException;
import ompca.vodcg.SystemElement;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.VariableOrientedDag;
import ompca.vodcg.condition.ParallelCondition;
import ompca.vodcg.condition.Proposition;
import ompca.vodcg.condition.VariablePlaceholder;
import ompca.vodcg.condition.data.Int;
import ompca.vodcg.condition.version.ThreadRole;

/**
 * @author Kao, Chen-yi
 *
 */
abstract public class OmpDirective 
extends SystemElement 
implements ASTAddressable, Comparable<OmpDirective>, Comparator<OmpDirective> {

	/**<pre>
	 * {@link https://www.openmp.org/wp-content/uploads/openmp-4.5.pdf}
	 * "12 Some OpenMP directives may be composed of consecutive #pragma 
	 * 	preprocessing directives if
	 * 	13 specified in their syntax."
	 */
	private static final Map<IASTStatement, NavigableSet<OmpDirective>> 
	DIRECTIVE_CACHE = new HashMap<>();
	
	/**
	 * The directive (pragma) address
	 */
	private IASTFileLocation address = null;
	private IASTStatement stat = null;
	
	private OmpParallel parallelRegion = null;
	private ParallelCondition condition = null;
	private Proposition race = null;

	
	
	protected OmpDirective(IASTFileLocation address, IASTStatement stat, 
			ParallelCondition pc, VODCondGen condGen) {
		super(condGen);

		if (address == null) throwNullArgumentException("address");
		if (stat == null) throwNullArgumentException("stat");
		if (pc == null) throwNullArgumentException("pc");
		
		this.address = address;
		this.stat = stat;
		condition = pc;
//		condition.addDirective(this);
	}
	
	
	
	public static NavigableSet<OmpDirective> from(final IASTStatement stat, final VODCondGen condGen) {
		return from(stat, null, condGen);
	}
	
	/**
	 * @param stat
	 * @param parallelRegion
	 * @param condGen
	 * @return an AST hierarchical set of OpenMP directives to <code>stat</code>
	 */
	public static NavigableSet<OmpDirective> from(final IASTStatement stat, OmpParallel parallelRegion, final VODCondGen condGen) {
		if (stat == null) throwNullArgumentException("statement");
		
//		DIRECTIVE_CACHE.clear();
		NavigableSet<OmpDirective> ds = DIRECTIVE_CACHE.get(stat);
		if (ds != null) return ds;
		if (DIRECTIVE_CACHE.containsKey(stat)) return null;
		
		final ASTRuntimeLocationComputer rlc = new ASTRuntimeLocationComputer(condGen);
		// 1) traversing stat itself without VOP at first
		IASTNode trvStat = stat;
		// searching directives backwards
		while (true) try {
			final IASTPreprocessorPragmaStatement pragma = rlc.previousOfAsIgnoring(
					trvStat, ASTUtil.AST_PRAGMA, ASTUtil.AST_COMMENT);
			final IASTStatement sbStat = rlc.previousOfAsIgnoring(
					trvStat, ASTUtil.AST_STATEMENT_TYPE, ASTUtil.AST_COMMENT);
			/* excluding the case: pragma -> sb (statement at the same function) -> stat
			 * !isAfterLocally = !(isAfter /\ isColocally) = isBefore || !isColocally 
			 * 	= (isBeforeLocally || isBeforeGlobally) || (isBeforeGlobally || isAfterGlobally)
			 * 	= isBeforeLocally || (isBeforeGlobally || isAfterGlobally) 
			 * 	= isBeforeLocally || !isColocally 
			 */
			if (pragma == null || tests(rlc.isBeforeLocally(pragma, sbStat)) 
					|| !ASTUtil.isCollocally(pragma, sbStat)) break;
		
			ParsingPragma: {
			String msg = OmpUtil.trimPragma(new String(pragma.getMessage()));
			if (msg.isEmpty()) break ParsingPragma;
			
			Matcher mDir = Pattern.compile("(?<omp>omp)\\s+" + "(" 
					+ "(?<parallel>parallel)" + "|" + "(?<for>for)" + "|" + "(?<simd>simd)" 
					+ "|" + "(?<master>master)" + "|" + "(?<single>single)" + "|" + "(?<task>task)"
					+ "|" + "(?<threadprivate>threadprivate)" 
					+ "|" + "(?<atomic>atomic)" + "|" + "(?<barrier>barrier)" + "|" + "(?<flush>flush)" 
					+ ")" + "\\s*" + "(?<clauses>.*)").matcher(msg);	// given that msg is trimmed
			if (!mDir.find() || mDir.group("omp") == null) break ParsingPragma;
			// TODO? Restrictions: ORDERED, COLLAPSE and SCHEDUL)E clauses may appear once each. 
			
			OmpDirective dir = null;
			final String clauses = mDir.group("clauses");
			final IASTFileLocation address = pragma.getFileLocation();
			final ParallelCondition pc = ParallelCondition.from(stat, dir, condGen);
			if (mDir.group("parallel") != null) 
				dir = OmpParallel.from(clauses, address, stat, pc, ds, condGen);
			else if (mDir.group("for") != null) {
				if (parallelRegion == null && ds != null) for (OmpDirective d : ds) 
					if (d instanceof OmpParallel) parallelRegion = (OmpParallel) d;
				dir = OmpFor.from(clauses, address, stat, parallelRegion, pc, condGen);
			}
			else if (mDir.group("simd") != null) 
				dir = OmpSimd.from(address, stat, pc, condGen);
			else if (mDir.group("master") != null) 
				dir = OmpMaster.from(address, stat, pc, condGen);
			else if (mDir.group("single") != null) 
				dir = OmpSingle.from(clauses, address, stat, pc, condGen);
			else if (mDir.group("task") != null) 
				dir = OmpTask.from(clauses, address, stat, pc, condGen);
			else if (mDir.group("threadprivate") != null) 
				dir = OmpThreadPrivate.from(clauses, address, stat, pc, condGen);
			else if (mDir.group("atomic") != null) 
				dir = OmpAtomic.from(address, stat, pc, condGen);
			else if (mDir.group("barrier") != null) 
				dir = OmpBarrier.from(address, stat, pc, condGen);
			else if (mDir.group("flush") != null) 
				dir = OmpFlush.from(clauses, address, stat, pc, condGen);
			else 
				throwTodoException(msg);

			assert pragma != null;
			if (dir == null) throwTodoException("null directive");
			if (ds == null) ds = new TreeSet<>(dir);
			if (!ds.add(dir)) throwTodoException("non-addable directive");
			}

			trvStat = pragma;
		} catch (Exception e) {
			throwTodoException(e);
		}

		// searching directives upwards
		addAllSkipNull(ds, ()-> fromCallerBlockOf(stat, condGen));
		
//		if (pc != null) pc.setDirectives(ds = Collections.unmodifiableList(ds));
		DIRECTIVE_CACHE.put(stat, ds);
		return ds;
	}
	
//	/**
//	 * @param forStat
//	 * @param pathCond
//	 * @return
//	 */
//	public static List<OmpDirective> from(IASTForStatement forStat, PathCondition pathCond) {
//		if (forStat == null) return null;
//		if (pathCond == null) VOPCondGen.throwTodoException("Create a path condition!");
//		
//		return from(forStat, pathCond.getCondGen());
//	}

	
	
	private static NavigableSet<OmpDirective> from(VariableOrientedDag vod, VODCondGen condGen) {
		assert vod != null;

		NavigableSet<OmpDirective> dirs = null;
		if (vod.hasTails()) {
			for (VariableOrientedDag tail : vod.getTails()) {
				final NavigableSet<OmpDirective> tailDirs = from(tail, condGen);
				if (dirs == null) dirs = tailDirs;
				else dirs.addAll(tailDirs);
			}
		}
		
		// 3) after all traversing the head
		IASTStatement parent = ASTUtil.getAncestorOfAs(
				vod.getCallee().getTopNode().getParent(), ASTUtil.AST_STATEMENT_TYPE, true);
		if (parent != null) {
			final NavigableSet<OmpDirective> headDirs = from(parent, condGen);
			if (dirs == null) dirs = headDirs;
			else dirs.addAll(headDirs);
		}
		return dirs;
	}
	
	public static OmpDirective fromEnclosing(final IASTStatement stat, final VODCondGen condGen) {
		return getSkipEmpty(dirs-> dirs.iterator().next(), ()-> from(stat, condGen));
	}
	
	private static NavigableSet<OmpDirective> fromCallerBlockOf(IASTStatement stat, VODCondGen condGen) {
		NavigableSet<OmpDirective> dirs = null;
		final IASTStatement oriStat = stat;
		while (true) {
			// directives always bind to block statements (within function bodies)
			IASTStatement parent = 
					ASTUtil.getAncestorOfAs(stat.getParent(), ASTUtil.AST_STATEMENT_TYPE, true);
			if (parent == null) break;
			dirs = guard(null, 
					()-> from(parent, condGen), ()-> Collections.emptyNavigableSet(), e-> throwTodoException(e), 
					parent);
			if (dirs != null) return dirs;
			stat = parent;
		}
		
		// 2) then traversing through VOP
		return from(VariableOrientedDag.from(
				ASTUtil.getNameOf(ASTUtil.getWritingFunctionDefinitionOf(oriStat)), null, condGen), 
				condGen);
	}
	
	public static NavigableSet<OmpDirective> fromReversedly(IASTStatement stat, VODCondGen condGen) {
		return from(stat, condGen).descendingSet();
//		return fromReversedly(from(stat, condGen));
	}
	
//	private static List<OmpDirective> fromReversedly(List<OmpDirective> dirs) {
//		if (dirs == null) return null;
//		if (dirs.isEmpty()) return dirs;
//		
//		List<OmpDirective> rdirs = new ArrayList<>(dirs);
//		Collections.reverse(rdirs);
//		return rdirs;
//	}
	
	
	
	@SuppressWarnings("unchecked")
	@Override
	protected <T extends SystemElement> T cloneChangeAddressTo(ASTAddressable newRtAddr) {
		final OmpDirective clone = (OmpDirective) super.cloneChangeAddressTo(newRtAddr);
		if (newRtAddr instanceof OmpDirective) address = ((OmpDirective) newRtAddr).getAddress();
		else throwTodoException("inconsistent addresses");
		return (T) clone;
	}
	
	@Override
	protected Object cloneNonConstant() {
		final OmpDirective clone = (OmpDirective) super.cloneNonConstant();
		clone.address = address;
		clone.stat = stat;
		clone.parallelRegion = parallelRegion;
		clone.condition = condition;
		clone.race = race;
		return clone;
	}

	
	
	@Override
	public ASTAddressable cacheRuntimeAddress() {
		return super.cacheRuntimeAddress();
	}
	
	public IASTFileLocation getAddress() {
		return address;
	}
	
	@Override
	public IASTNode getASTAddress() {
		return getStatement();
	}
	
	@Override
	public String getShortAddress() {
		return ASTUtil.toLineLocationOf(address);
	}
	
	public IASTStatement getStatement() {
		return stat;
	}
	
	public Proposition getStatementProposition() {
		return Proposition.fromRecursively(getStatement(), getRuntimeAddress(), getCondGen());
	}
	
	protected void setStatement(IASTStatement newStat) {
		stat = newStat;
	}
	
	public ParallelCondition getCondition() {
		assert condition != null;
		if (condition.isEmpty()) condition.and(()-> generateAssertion());
		return condition;
	}
	
	final public ParallelCondition peekCondition() {
		return condition;
	}
	
	/**
	 * Parallel region is fundamental to any other directive.
	 * @return
	 * @throws Exception 
	 */
	public OmpParallel getParallelRegion() {
		if (parallelRegion != null) return parallelRegion;
		
		OmpDirective d = this;
		do {
			d = d.previous();
//			else if (p != dp) 
//				VOPCondGen.throwTodoException("p = getCommonParallelRegion(p, dp);?");
		} while (!(d instanceof OmpParallel) && d != null);
		setParallelRegion((OmpParallel) d);
		return parallelRegion;
	}
	
	/**
	 * @param parallelRegion
	 */
	protected void setParallelRegion(OmpParallel parallelRegion) {
		if (parallelRegion == null) throwNullArgumentException("parallel region");
		
		this.parallelRegion = parallelRegion;
	}


	
	/**
	 * pre ::= numThreads > 1 /\ 0 <= t < numThreads
	 * 
	 * @return non-null
	 */
	public Proposition getPrecondition() {
		final VariablePlaceholder<?> t1 = condition.getThread(ThreadRole.THREAD1),	// thread1
				t2 = condition.getThread(ThreadRole.THREAD2),						// thread2
				nts = condition.getNumThreads();
		return Int.ONE.lessThan(nts)
				.and(()-> Int.ZERO.lessEqual(t1).and(()-> t1.lessThan(nts)))
				.and(()-> Int.ZERO.lessEqual(t2).and(()-> t2.lessThan(nts)));
	}
	
	/**
	 * @return including meta-assertion of parallel condition
	 */
	protected Proposition generateAssertion() {
		return getPrecondition().and(getCondition().getAssertion());
	}

	/**
	 * @return Disjunction of sub-cached race conditions.
	 */
	final public Proposition generateRaceAssertion() {
		if (race != null) return race;
		
		final Proposition cache = guard(
				()-> cacheRaceAssertion(), ()-> null);
		race = race == null ? cache : race.orSkipNull(cache);
		return race;
	}
	
	protected Proposition cacheRaceAssertion() {
		return getSkipNull(()-> 
		getParallelRegion().generateRaceAssertion());
	}
	
	final public void addRaceAssertion(Proposition newAssert) {
		if (newAssert == null) throwNullArgumentException("new race");
		race = race == null ? newAssert : race.and(newAssert);
	}
	
	
	
	@SuppressWarnings("unchecked")
	@Override
	public OmpDirective previous() {
		final VODCondGen cg = getCondGen();

		// directly hierarchical previous directive
		final OmpDirective preHier = from(stat, cg).lower(this);	
		if (preHier != null && preHier.getStatement() == stat) return preHier;
		
		// sibling directive
		return getSkipNull(()-> from(new ASTRuntimeLocationComputer(cg)
				.previousOfAsIgnoring(stat, ASTUtil.AST_STATEMENT_TYPE, ASTUtil.AST_COMMENT), cg)
				.last());	

//		// searching directives backwards
//		OmpDirective pd = null;
//		for (OmpDirective d : from(stat, cg)) {
//			if (d == this) {
//				if (pd == null) break;
//				return pd;
//			}
//			pd = d; 
//		}
//		
//		// searching directives upwards
//		return getSkipNull(()-> fromCallerBlockOf(stat, cg).lower(this));
	}


	
	static public boolean hasAny() {
		return !DIRECTIVE_CACHE.isEmpty();
	}
	
	public boolean isAtomic() {
		return false;
	}
	
	@Override
	protected Boolean cacheConstant() {
		return getSkipNull(()-> condition.isConstant());
	}

	
	
	@Override
	public int compare(OmpDirective dir1, OmpDirective dir2) {
		if (dir1 == dir2) return 0;
		if (dir1 == null) dir2.throwIncomparableException(null);	
		
		return dir1.compareTo(dir2);
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Comparable#compareTo(java.lang.Object)
	 */
	@Override
	public int compareTo(OmpDirective dir2) throws IncomparableException {
		if (dir2 == null) throwIncomparableException(null);	
		return new ASTRuntimeLocationComputer(getCondGen())
				.compare(address, dir2.address);
	}

	<T> T throwIncomparableException(OmpDirective dir2) {
		throw new IncomparableException(this, dir2, "directives", null);
	}
	

	
	/**
	 * @return only meta-assertion, excluding the statement condition
	 */
	public Proposition toProposition() {
		return generateAssertion();
	}

	public String toString() {
		return ASTUtil.toStringOf(stat);
	}
	
}