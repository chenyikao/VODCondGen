/**
 * 
 */
package ompca.vodcg.parallel;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.NavigableSet;
import java.util.Set;
import java.util.function.Supplier;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.vodcg.Assignable;
import ompca.vodcg.AssignableElement;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.FunctionalPathVariable;
import ompca.vodcg.condition.ParallelCondition;
import ompca.vodcg.condition.PathVariable;
import ompca.vodcg.condition.PathVariablePlaceholder;
import ompca.vodcg.condition.Proposition;
import ompca.vodcg.condition.Referenceable;
import ompca.vodcg.condition.VariablePlaceholder;
import ompca.vodcg.condition.version.NoSuchVersionException;
import ompca.vodcg.condition.version.ThreadPrivateVersion;
import ompca.vodcg.condition.version.ThreadRole;
import ompca.vodcg.condition.version.ThreadRoleMatchable;
import ompca.vodcg.condition.version.Version;
import ompca.vodcg.condition.version.VersionEnumerable;

/**
 * This kind of directive only privatizes path variables hence affects only path conditions
 * but no parallel ones.
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public abstract class OmpThreadPrivatizable extends OmpFlushable {

//	final private Map<String, PathVariable> 
//	privatizedVars = new HashMap<>();
	/**
	 * The path variable of placeholder's may be changed over time
	 * since {@link PathVariable} may be upgraded to {@link FunctionalPathVariable}.
	 */
	final private Set<PathVariablePlaceholder> privatizedPlaceholders = new HashSet<>();

	private Supplier<Proposition> preCond = null;

	protected OmpThreadPrivatizable(
			IASTFileLocation address, IASTStatement blockStat, boolean nowait, ParallelCondition pc, 
			VODCondGen condGen) {
		super(address, blockStat, nowait, pc, condGen);
//		preCond = new PathCondition(condGen);
	}

	
	
	@Override
	protected Proposition cacheRaceAssertion() {
		Proposition race = super.cacheRaceAssertion(),
				statProp = getStatementProposition();
		if (statProp != null) {
			final Set<Version<?>> pvs = getPrivatizedVariableReferences();
			for (Version<?> v : statProp.getDirectVariableReferences()) {

				// non-privately-declared shared race
				if (!Version.contains(pvs, v)) {
					final VersionEnumerable<?> ve = v.getAddress();
					if (ve instanceof AssignableElement) {
						final Assignable<?> asn = ((AssignableElement) ve).getAssignable();
				
						// exists some assigned
						if (tests(asn.isAssigned()) && !asn.isThreadPrivate() 
								&& !asn.isArray() && !asn.isLoopIterator()) {
							Supplier<Proposition> subRace = generateNonAtomicRace(asn, v.getThreadRole());
							if (subRace == null) continue;
							race = race == null ? subRace.get() : race.or(subRace);
						}
					
					} else throwTodoException("unsupported version enumerable");
				}
			}
		}
		return race;
	}
	
	/**
	 * For example exists i1, i2, i1 != i2 && tmp[i1] = a[i1]+i1 && tmp[i2] = a[i2]+i2 && a[i1] = tmp[i2] && a[i1] = a[i2]+i2, given
	 * 
	 * #pragma omp parallel for
	 * for (i=0;i<len;i++)
	 * {
	 * 	tmp =a[i]+i;
	 * 	a[i] = tmp;
	 * }
	 * 
	 * @param <Sbj>
	 * @param asn - for example tmp.
	 * @param role
	 * @return
	 * @throws NoSuchVersionException
	 */
	private <Sbj extends Referenceable> Supplier<Proposition> generateNonAtomicRace(
			final Assignable<?> asn, ThreadRoleMatchable role) throws NoSuchVersionException {
		assert asn != null && role != null;
		final NavigableSet<OmpDirective> dirs = asn.getEnclosingDirectives();
		
		// exists some OpenMP directive
		if (!dirs.isEmpty()) {
			final ArithmeticExpression asner = asn.getAssignerIf().toArithmeticExpression();
			
			// exists functional assigner
			if (asner.isFunctional()) {
				final IASTStatement stat = dirs.first().getStatement();
				if (stat instanceof IASTForStatement) {
					final VODCondGen cg = asn.getCondGen();
					final IASTForStatement forStat = (IASTForStatement) stat;
					final PathVariablePlaceholder asd = asn.getPathVariablePlaceholder(),
							i = Assignable.fromCanonicalIteratorOf(forStat, asn.getRuntimeAddress(), cg).getPathVariablePlaceholder();
					final Version<?> asd1i1 = asd.getVersion(ThreadRole.THREAD1), asd1i2 = asd.getVersion(ThreadRole.THREAD2); 
					for (Assignable<?> asn2 : asn.next().getAssigneds())
						
						// exists non-atomic assignments
						if (!asn.isAtomicTo(asn2)) {
							final VariablePlaceholder<?> i1 = i.cloneReversion(forStat, ThreadRole.THREAD1, null),
									i2 = i.cloneReversion(forStat, ThreadRole.THREAD2, null),
									asd2 = asn2.getPathVariablePlaceholder().cloneReversion(forStat, ThreadRole.THREAD1, null);
							final ArithmeticExpression asner1 = asner.cloneReversion(forStat, ThreadRole.THREAD1, null),
									asner2 = asner.cloneReversion(forStat, ThreadRole.THREAD2, null);
							// i1 != i2 && 
							return ()-> i1.equal(i2).not().and(()-> 
							// tmp[i1] = a[i1]+i1 && tmp[i2] = a[i2]+i2 && a[i1] = tmp[i2] && a[i1] = a[i2]+i2
							asd1i1.equal(asner1)).and(()-> asd1i2.equal(asner2)).and(()-> asd2.equal(asd1i2)).and(()-> asd2.equal(asner2));
						}
					
				} else throwTodoException("unsupported statment");
			}
		}
		
		return null;
	}
	
	
	
	protected Proposition initPrecondition(
			final Assignable<?> iAsn, final IASTStatement block, final List<ArithmeticExpression> functionArgv) {
		final Assignable<?> piAsn = iAsn.previous();
		if (piAsn != null) try {	// pilv == null => this variable is initially privatized
			final PathVariablePlaceholder pp = PathVariablePlaceholder.from(piAsn);
			final Version<? extends PathVariable> iv1 = ThreadPrivateVersion.fromThread1(iAsn, block, functionArgv),
					iv2 = ThreadPrivateVersion.fromThread2(iAsn, block, functionArgv);
			return iv1.equal(pp).and(()-> iv2.equal(pp));
			
		} catch (NoSuchVersionException e) {
			return throwTodoException(e);
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
		return null;
	}
	
	/**
	 * pre ::= privatized delegate initialization
	 * 
	 * @return
	 */
	@Override
	public Proposition getPrecondition() {
		if (preCond == null) throwTodoException("empty condition");
		
		final Proposition prePre = super.getPrecondition();
		return prePre == null
				? throwTodoException("empty condition")
				: prePre.and(preCond);
	}
	

	
	/**
	 * @return non-null
	 */
	public Set<PathVariable> getPrivatizedVariables() {
		final Set<PathVariable> pvs = new HashSet<>();
		for (PathVariablePlaceholder pp : getPrivatizedPlaceholders())
			pvs.add(pp.getVariable());
		
		// parent privatized path variables
		final OmpParallel op = getParallelRegion();
		if (op != null && op != this) pvs.addAll(op.getPrivatizedVariables());
		
		return Collections.unmodifiableSet(pvs);
	}
	
	public PathVariable getPrivatizedVariable(final String vName) {
		if (vName == null) throwNullArgumentException("name");
		
		for (PathVariable pv : getPrivatizedVariables())
			if (pv.equalsName(vName)) return pv;
		return null;
	}
	
	/**
	 * @return non-null
	 */
	public Set<Version<?>> getPrivatizedVariableReferences() {
		final Set<Version<?>> pvrs = new HashSet<>();
		for (PathVariablePlaceholder pp : getPrivatizedPlaceholders()) 
			pvrs.add(pp.getVersion());
		return pvrs;
	}
	
	/**
	 * @return non-null
	 */
	public Set<PathVariablePlaceholder> getPrivatizedPlaceholders() {
		return privatizedPlaceholders;
//		final Set<PathVariablePlaceholder> pps = new HashSet<>(privatizedPlaceholders);
//		
//		// parent privatized path variable placeholder's
//		final OmpParallel pr = getParallelRegion();
//		if (pr != null && pr != this) guard(
//				()-> pps.addAll(pr.getPrivatizedPlaceholders()),
//				()-> false);
//		
//		return Collections.unmodifiableSet(pps);
	}
	
	public Set<PathVariablePlaceholder> getPrivatizedPlaceholders(
			PathVariable v) {
		if (v == null) throwNullArgumentException("path variable");
		
		final Set<PathVariablePlaceholder> pps = new HashSet<>();
		for (PathVariablePlaceholder pp : getPrivatizedPlaceholders())
			if (v.equals(pp.getVariable())) pps.add(pp);
		return pps;
	}
	
	protected Set<PathVariablePlaceholder> getPrivatizedArrayEnclosers() {
		final Set<PathVariablePlaceholder> paes = new HashSet<>();
		for (PathVariablePlaceholder pvp : getPrivatizedPlaceholders()) try {
			addSkipNull(paes, ()-> pvp.getArrayEncloser());
		} catch (Exception e) {
			throwTodoException(e);
		}
		return paes;
	}

	protected Assignable<?> privatize(final String vName) {
		Assignable<?> iAsn = null;
		for (Assignable<?> asn : Assignable.fromOf(getStatement(), vName, getRuntimeAddress(), getCondGen())) {
			final PathVariablePlaceholder vp = PathVariablePlaceholder.from(asn);
			if (iAsn == null || tests(asn.isBeforeLocally(iAsn))) iAsn = asn;
			privatizedPlaceholders.add(vp);
		}
		return iAsn;
	}
	
	public void privatize(PathVariable pv, final List<ArithmeticExpression> functionArgv) {
		privatize(pv.getName(), functionArgv);
	}
	
	/**
	 * Privatization by caching the path condition variable named {@code vName} and
	 * reversioning the its delegates corresponding to directive's block statement.
	 * 
	 * @param vName
	 * @param functionArgv
	 */
	@SuppressWarnings("unchecked")
	public PathVariable privatize(
			final String vName, final List<ArithmeticExpression> functionArgv) {
		if (vName == null) throwNullArgumentException("variable");
		
//		PathVariable v = getPrivatizedVariable(vName);
//		if (v != null) return v;

		final Assignable<?> iAsn = privatize(vName);	// for initializer placeholder
		if (iAsn == null) throwTodoException(vName + " is not a path variable");
		
		// initializing private variables
		preCond = ()-> initPrecondition(iAsn, getStatement(), functionArgv);
		
//		privatizedVars.put(vName, v);
		return PathVariable.from((Assignable<PathVariable>) iAsn);
	}
	
	public List<PathVariable> parseAndPrivatize(String clauses) {
		return parseAndPrivatize(clauses, null);
	}
	
	/**
	 * @param clauses
	 * @return path variables <em>only</em> privatized by this method
	 */
	public List<PathVariable> parseAndPrivatize(String clauses, final List<ArithmeticExpression> privateArgv) {
		if (clauses == null) throwNullArgumentException("clauses");
		
		final Matcher mList = Pattern.compile(
				OmpUtil.patternList(null, "firstListItem", "listItem")).matcher(clauses);
//		final StarMatcher mList = new StarMatcher(Pattern.compile(
//				OmpUtil.patternList(null, "firstListItem", "listItem")), clauses);
		final List<PathVariable> pvs = new ArrayList<>();
		if (mList.find()) for (String li : clauses.split(OmpUtil.patternComma()))
			pvs.add(privatize(li, privateArgv));
		/*
		 * https://stackoverflow.com/questions/25858345/getting-match-of-group-with-asterisk
		 */
//		if (mList.find()) pvs.add(privatize(mList.group("firstListItem"), privateArgv));
//		while (mList.find()) pvs.add(privatize(mList.group("listItem"), privateArgv));
		return pvs;
	}

}