/**
 * 
 */
package ompca.vodcg.parallel;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.vodcg.ASTAddressable;
import ompca.vodcg.ASTException;
import ompca.vodcg.Assignable;
import ompca.vodcg.IncomparableException;
import ompca.vodcg.UncertainPlaceholderException;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.And;
import ompca.vodcg.condition.Arithmetic;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.Equality;
import ompca.vodcg.condition.ExpressionRange;
import ompca.vodcg.condition.ParallelCondition;
import ompca.vodcg.condition.PathVariable;
import ompca.vodcg.condition.PathVariablePlaceholder;
import ompca.vodcg.condition.Proposition;
import ompca.vodcg.condition.VariablePlaceholder;
import ompca.vodcg.condition.data.Int;
import ompca.vodcg.condition.version.FunctionallableRole;
import ompca.vodcg.condition.version.NoSuchVersionException;
import ompca.vodcg.condition.version.ThreadPrivateVersion;
import ompca.vodcg.condition.version.ThreadRole;
import ompca.vodcg.parallel.OmpUtil.Schedule;

/**<pre>
 * Index segmentation:
 * 
 * if (schedule == STATIC) ...
 * 	(t, j) =	(1, jbeg), (1, jbeg+1), ... (1, jbeg+chunkSize-1), ...,
 * 				(2, jbeg+chunkSize), (2, jbeg+chunkSize+1), ... (2, jbeg+chunkSize*2-1), 
 * 				...
 * 				(numThreads, jbeg+chunkSize*(numThreads-1)), ...,
 * 				(numThreads, jbeg+chunkSize*(numThreads-1)+chunk_t), ..., 
 * 				(numThreads, jbeg+chunkSize*numThreads-1)
 * 	::=	pre(For) -> j_t = jbeg+chunkSize*(t-1)+chunk_t 
 * 
 * With reduction:
 * 
 * if (schedule == STATIC) ...
 * 	(frc1, j) = (frc1(1), jbeg), (frc1(1), jbeg+1), ... (frc1(1), jbeg+chunkSize-1), ...,
 * 				(frc1(2), jbeg+chunkSize), (frc1(2), jbeg+chunkSize+1), ... (frc1(2), jbeg+chunkSize*2-1), 
 * 				...
 * 				(frc1(numThreads), jbeg+chunkSize*(numThreads-1)), 
 * 				(frc1(numThreads), jbeg+chunkSize*(numThreads-1)+1), ..., 
 * 				(frc1(numThreads), jbeg+chunkSize*numThreads-1)
 * 	::=	pre(For) -> j_t = jbeg+chunkSize*(t-1)+chunk_t /\ frc1(t) = ??[j_t]
 * 
 * </pre>
 * 
 * @see https://computing.llnl.gov/tutorials/openMP
 * 
 * @author Kao, Chen-yi
 * 
 */
@SuppressWarnings("deprecation")
public class OmpFor extends OmpReduceable {

	private class LoopCollector extends ASTVisitor {
		private int collapseCount;
		
		private LoopCollector(int collapse) {
			collapseCount = collapse;
			shouldVisitStatements = true;
		}

		public int visit(IASTStatement stat) {
			if (collapseCount > 0 && stat instanceof IASTForStatement) {
				collapse.add((IASTForStatement) stat);
				collapseCount--;
			}
			return PROCESS_CONTINUE;
		}
	}

	
	
	/**<pre>
	 * (Page 58 OpenMP API – Version 4.5 November 2015)
	 * 25 The collapse clause may be used to specify how many loops are associated with the loop
	 * 26 construct. The parameter of the collapse clause must be a constant positive integer expression.
	 * 27 If a collapse clause is specified with a parameter value greater than 1, then the iterations of the
	 * 28 associated loops to which the clause applies are collapsed into one larger iteration space that is then
	 * 29 divided according to the schedule clause. The sequential execution of the iterations in these
	 * 30 associated loops determines the order of the iterations in the collapsed iteration space. If no
	 * 31 collapse clause is present or its parameter is 1, the only loop that is associated with the loop
	 * (Page 59 OpenMP API – Version 4.5 November 2015)
	 * 1 construct for the purposes of determining how the iteration space is divided according to the
	 * 2 schedule clause is the one that immediately follows the loop directive.
	 */
	final private List<IASTForStatement> collapse = new ArrayList<>();

	private Schedule schedule = null;



	/**<pre>
	 * @param address
	 * @param parallelRegion
	 * @param collapse
	 * @param nowait
	 * @param stat
	 * @param pc
	 * @param condGen
	 */
	private OmpFor(IASTFileLocation address, OmpParallel parallelRegion, int collapse, boolean nowait, 
			IASTForStatement stat, ParallelCondition pc, VODCondGen condGen) {
		super(null, address, stat, nowait, pc, condGen);
		
		assert collapse > 0;
		stat.accept(new LoopCollector(collapse));	// nested for-loop traversal
		
		setParallelRegion(parallelRegion);
	}
	
	
	
	protected static OmpFor from(String clauses, IASTFileLocation address, 
			IASTStatement blockStat, OmpParallel parallelRegion, 
			ParallelCondition pc, VODCondGen condGen) {
		if (clauses == null) return throwNullArgumentException("clause");
		if (address == null) return throwNullArgumentException("file location");
		if (blockStat == null) return throwNullArgumentException("statement");
		if (pc == null) return throwNullArgumentException("parallel condition");
		if (condGen == null) return throwNullArgumentException("condition generator");
		
		if (blockStat instanceof IASTForStatement) return from(
				clauses, address, (IASTForStatement) blockStat, parallelRegion, pc, condGen);
		
		return null;
	}
	
	
	
	protected static OmpFor from(String clauses, IASTFileLocation address, 
			IASTForStatement forStat, OmpParallel parallelRegion, 
			ParallelCondition pc, VODCondGen condGen) {
		if (clauses == null) return throwNullArgumentException("clause");
		if (address == null) return throwNullArgumentException("file location");
		if (forStat == null) return throwNullArgumentException("for-loop");
		if (pc == null) return throwNullArgumentException("parallel condition");
		if (condGen == null) return throwNullArgumentException("condition generator");
		
		/**<pre>
		 * {@link https://www.openmp.org/wp-content/uploads/openmp-4.5.pdf}
		 * "?? This assumes a parallel region has already been initiated, 
		 * 	?? otherwise it executes in serial on a single processor."
		 * 
		 * Calling OmpFor.from(...) implies that forStat is coupled with a 
		 * 'for' pragma rather than a 'parallel' one.
		 */
		if (parallelRegion == null) 
			parallelRegion = OmpParallel.from(forStat.getParent(), condGen);
		if (parallelRegion == null) {
//			VOPCondGen.throwTodoException("No parallel regions?");
			return null;
		}
		
		// TODO? "Restrictions: ORDERED, COLLAPSE and SCHEDULE clauses may appear once each." 
		Matcher mFor = Pattern.compile("("
				+ OmpUtil.patternSchedule("schedule", null, null) 				+ "|" 
				+ OmpUtil.patternOrdered("ordered") 							+ "|" 
				+ OmpUtil.patternPrivate("private", null, null, null)			+ "|" 
				+ OmpUtil.patternFirstPrivate("firstprivate", null, null, null) + "|" 
				+ OmpUtil.patternLastPrivate("lastprivate", null, null, null)	+ "|" 
				+ OmpUtil.patternShared("shared", null, null, null)				+ "|" 
				+ OmpUtil.patternReduction("reduction", null, null, null, null)	+ "|" 
				+ OmpUtil.patternCollapse("collapse", "n")						+ "|" 
				+ OmpUtil.patternNoWait("nowait")								+ "|" 
				+ "\\s" + ")+").matcher(clauses);

		String clauseSchedule = null, clausePrivate = null, clauseFirstPrivate = null, 
				clauseLastPrivate = null, clauseShared = null, clauseReduction = null; 
		int collapse = 1;
		boolean ordered = false, nowait = false;
		while (mFor.find()) {
			if (clauseSchedule == null) clauseSchedule = mFor.group("schedule");
			if (!ordered) ordered = mFor.group("ordered") != null; 
			if (clausePrivate == null) clausePrivate = mFor.group("private");
			if (clauseFirstPrivate == null) clauseFirstPrivate = mFor.group("firstprivate");
			if (clauseLastPrivate == null) clauseLastPrivate = mFor.group("lastprivate"); 
			if (clauseShared == null) clauseShared = mFor.group("shared");
			if (clauseReduction == null) clauseReduction = mFor.group("reduction");
			if (mFor.group("collapse") != null) collapse = new Integer(mFor.group("n"));
			if (!nowait) nowait = mFor.group("nowait") != null;
		}
		return from(parallelRegion, clauseSchedule, ordered, clausePrivate, clauseFirstPrivate, 
				clauseLastPrivate, clauseShared, clauseReduction, collapse, nowait, 
				address, forStat, pc, condGen);
	}

	
	
	protected static OmpFor from(OmpParallel parallelRegion, String clauseSchedule, boolean ordered, 
			String clausePrivate, String clauseFirstPrivate, String clauseLastPrivate, 
			String clauseShared, String clauseReduction, boolean nowait, 
			IASTFileLocation address, IASTForStatement forStat, ParallelCondition pc, VODCondGen condGen) {
		return from(parallelRegion, clauseSchedule, ordered, clausePrivate, clauseFirstPrivate, 
				clauseLastPrivate, clauseShared, clauseReduction, 1, nowait, 
				address, forStat, pc, condGen);
	}
	
	protected static OmpFor from(OmpParallel parallelRegion, String clauseSchedule, boolean ordered, 
			String clausePrivate, String clauseFirstPrivate, String clauseLastPrivate, 
			String clauseShared, String clauseReduction, int collapse, boolean nowait, 
			IASTFileLocation address, IASTForStatement forStat, ParallelCondition pc, VODCondGen condGen) {
		if (collapse < 1) throwInvalidityException("non-natural collapse");

		final OmpFor of = new OmpFor(address, parallelRegion, collapse, nowait, forStat, pc, condGen);

		if (clauseSchedule != null) {
			final Matcher mSchedule = Pattern.compile(OmpUtil.patternSchedule(null, "type", "chunk"))
					.matcher(clauseSchedule); 
			while (mSchedule.find()) {
				final String typeClause = mSchedule.group("type"), chunkClause = mSchedule.group("chunk");
				if (typeClause != null) of.setSchedule(OmpUtil.Schedule.from(typeClause));
				if (chunkClause != null) throwTodoException("unsupported chunk");
			}
		} else	// including !mFor.find()
			of.setSchedule(OmpUtil.Schedule.STATIC);	// TODO: "the default schedule is implementation dependent"

		List<ArithmeticExpression> pArgv = null;
		if (clausePrivate != null && !clausePrivate.isBlank()) {
			final Matcher mPrivate = Pattern.compile(OmpUtil.patternPrivate(null, "privateList", null, null))
					.matcher(clausePrivate);
			if (mPrivate.find()) {
				final List<PathVariable> pvs = of.parseAndPrivatize(mPrivate.group("privateList")); 
				if (pvs != null && !pvs.isEmpty()) pArgv = new ArrayList<>();
			} else throwTodoException("empty private list");
		}
		try {
			/* <q>A list item may not appear in a lastprivate clause 
			 * unless it is the loop iteration variable of a loop 
			 * that is associated with the construct.</q>
			 * (https://www.openmp.org/spec-html/5.0/openmpsu44.html#x67-1880002.9.5)
			 */
			final PathVariablePlaceholder it = PathVariablePlaceholder.fromCanonicalIteratorOf(forStat, of, condGen);
			if (it == null) throwTodoException("non-canonical loop");
			of.privatize(it.getVariable(), null);
			
		} catch (UncertainPlaceholderException | ASTException | IncomparableException | NoSuchVersionException e) {
			throwTodoException(e);
		}
		
		if (clauseFirstPrivate != null) throwTodoException("first private list");	// "firstPrivateList") != null);
//		Matcher mFirstPrivate = Pattern.compile(OmpUtil.patternFirstPrivate(null, "firstPrivateList", null) 	+ "|" 
//				+ OmpUtil.patternLastPrivate("lastprivate", "lastPrivateList", null)		+ "|" 
//				+ OmpUtil.patternShared("shared", "sharedList", null)						+ "|" 
		
		if (clauseLastPrivate != null) throwTodoException("first private list");	// "lastPrivateList") != null);
		
		if (clauseShared != null) throwTodoException("shared list");		// "sharedList") != null);
		
		if (clauseReduction != null) of.reduce(clauseReduction, pArgv);

		return of;
	}
	
	

	@Override
	protected Proposition generateAssertion() {
		Proposition superAss = super.generateAssertion(), 
				lgAss = getLoopGeneralAssertion();
		return superAss == null 
				? lgAss
				: (lgAss == null ? superAss : superAss.and(()-> lgAss));
	}

	/**
	 * @see ompca.vodcg.parallel.OmpThreadPrivatizable#generateRaceAssertion()
	 */
	@Override
	protected Proposition cacheRaceAssertion() {
		if (getPrivatizedVariables().contains(
				PathVariable.getIteratorOf(getForStatement(), getRuntimeAddress(), getCondGen())))
			return super.cacheRaceAssertion();
		
		throwTodoException("loop iterator or array indices are non-privatized (shared)");
		return null;
	}
	
	
	
	@Override
	protected Proposition initPrecondition(
			final Assignable<?> iAsn, final IASTStatement block, final List<ArithmeticExpression> functionArgv) {
		final Proposition er = ExpressionRange.fromIteratorOf(block, iAsn.getRuntimeAddress(), getCondGen());
		try {
			return ((Proposition) er.cloneReversion(block, ThreadRole.THREAD1, null)).and(
					(Proposition) er.cloneReversion(block, ThreadRole.THREAD2, null));
			
		} catch (Exception e) {
			return throwTodoException(e);
//			return throwUnhandledException(e);
		}
	}

	@Override
	public ParallelCondition getCondition() {
		final ParallelCondition cond = super.getCondition();
		
		// adding general loop condition
		cond.and(()-> getLoopGeneralAssertion());
		// adding loop reduction condition
		cond.and(this);
		return cond;
	}
	
	/**
	 * pre(For) ::= chunk > 0 
	 * 
	 * @return
	 */
	@Override
	public Proposition getPrecondition() {
		Proposition pre = super.getPrecondition(), 
				preFor = Int.ZERO.lessThan(peekCondition().getChunkSize());
		return pre == null 
				? preFor 
				: (preFor == null ? pre : pre.and(()-> preFor));
	}
	
	@Override
	public Set<PathVariablePlaceholder> getPrivatizedPlaceholders() {
		if (super.getPrivatizedPlaceholders().isEmpty()) privatize(
				Assignable.fromCanonicalInitializedIteratorOf(
						(IASTForStatement) getStatement(), getRuntimeAddress(), getCondGen()).getName());
		return super.getPrivatizedPlaceholders();
	}

	public List<IASTForStatement> getLoops() {
		return collapse;
	}
	
	public Proposition getLoopGeneralAssertion() {
		Proposition result = null;
		for (IASTForStatement l : getLoops()) {
			Supplier<Proposition> lr = ()-> getLoopGeneralAssertion(l);
			result = result == null ? lr.get() : result.and(lr);
		}
		return result;
	}
	
	/**<pre>
	 * General parallel loop invariants:
	 * 
	 * a) Index segmentation
	 * 
	 * In local chunk variable:
	 * if (schedule.kind == static) [round-robin]...
	 * 	(t, j) =	(1, jbeg), (1, jbeg+1), ... (1, jbeg+chunkSize-1), ...,
	 * 				(2, jbeg+chunkSize), (2, jbeg+chunkSize+1), ... (2, jbeg+chunkSize*2-1), 
	 * 				...,
	 * 				(numThreads, jbeg+chunkSize*(numThreads-1)), ...,
	 * 				(numThreads, jbeg+chunkSize*(numThreads-1)+local_chunk_t), ..., 
	 * 				(numThreads, jbeg+chunkSize*numThreads-1),
	 * 				(1, jbeg+chunkSize*numThreads), ...,
	 * 				(1, jbeg+chunkSize*numThreads+local_chunk_t), ..., 
	 * 				(1, jbeg+chunkSize*(numThreads+1)-1),
	 * 				...
	 * 	::=	pre(For) -> j_t = ??jbeg+chunkSize*(t-1)+local_chunk_t 
	 * 
	 * if (schedule.kind == dynamic) ...
	 * 	(t, j) =	(1, jbeg), (1, jbeg+1), ... (1, jbeg+chunkSize-1), ...,
	 * 				(2, jbeg+chunkSize), (2, jbeg+chunkSize+1), ... (2, jbeg+chunkSize*2-1), 
	 * 				...,
	 * 				(numThreads, jbeg+chunkSize*(numThreads-1)), ...,
	 * 				(numThreads, jbeg+chunkSize*(numThreads-1)+local_chunk_t), ..., 
	 * 				(numThreads, jbeg+chunkSize*numThreads-1)
	 * 				(t, jbeg+chunkSize*numThreads), ...,
	 * 				(t, jbeg+chunkSize*numThreads+local_chunk_t), ..., 
	 * 				(t, jbeg+chunkSize*(numThreads+1)-1),
	 * 				...
	 * 	::=	pre(For) -> j_t = ??jbeg+chunkSize*(t-1)+local_chunk_t 
	 * 
	 * if (schedule.kind == guided) ...
	 * if (schedule.kind == auto) ...
	 * if (schedule.kind == runtime) ...
	 * 
	 * 
	 * 
	 * In global chunk variable: jbeg+chunkT*chunkSize <= j_t <= jbeg+(chunkT+1)*chunkSize 
	 * 
	 * Ignoring TODO: ICV def-sched-var.
	 * 
	 * if (schedule.kind == static) [round-robin]... 
	 * 	(t, chunkT) =	(0, 1), (0, 2), ..., (0, chunkSize), 
	 * 					(1, chunkSize+1), (1, chunkSize+2), ..., (1, chunkSize*2), 
	 * 					...,
	 * 					(numThreads-1, chunkSize*(numThreads-1)+1), 
	 * 					(numThreads-1, chunkSize*(numThreads-1)+2), ..., 
	 * 					(numThreads-1, chunkSize*numThreads), 
	 * 					(0, chunkSize*numThreads+1), 
	 * 					(0, chunkSize*numThreads+2), ...,
	 * 					(0, chunkSize*(numThreads+1)), 
	 * 					...,
	 * 					(t, chunkSize*(numThreads*n+t)+1), 
	 * 					(t, chunkSize*(numThreads*n+t)+2), ...,
	 * 					(t, chunkSize*(numThreads*n+t+1)), 
	 * 					...
	 *  
	 * TODO: if (schedule.kind == dynamic) ...
	 * TODO: if (schedule.kind == guided) ...
	 * TODO: if (schedule.kind == auto) ...
	 * TODO: if (schedule.kind == runtime) ...
	 * 
	 * In Z3-SMT:
	 * 
	((_chunk1 Int)(_chunk2 Int)(_j1 Int)(_j2 Int)(_chunk_size Int)(_nthreads Int)(_x Int)(_jst Int)(_jend Int)) Bool 
	(and
	  (<= MIN _chunk1)    (<= _chunk1 MAX)
	  (<= MIN _chunk2)    (<= _chunk2 MAX)
	  (<= MIN _j1)        (<= _j1 MAX)
	  (<= MIN _j2)        (<= _j2 MAX)
	  (<= MIN _chunk_size)(<= _chunk_size MAX)
	  (<= MIN _nthreads)  (<= _nthreads MAX)
	  (<= MIN _x)         (<= _x MAX)
	  (<= MIN _jst)       (<= _jst MAX)
	  (<= MIN _jend)      (<= _jend MAX)
	
	  ;jst+chunk1*chunkSize <= j1 < jst+(chunk1+1)*chunkSize,  jst+chunk2*chunkSize <= j2 < jst+(chunk2+1)*chunkSize, 
	  (<= (+ _jst (* _chunk1 _chunk_size)) _j1)(< _j1 (+ _jst (* (+ _chunk1 1) _chunk_size)))
	  (<= (+ _jst (* _chunk2 _chunk_size)) _j2)(< _j2 (+ _jst (* (+ _chunk2 1) _chunk_size)))
	  (add_guard _jst (* _chunk1 _chunk_size))
	  (mul_guard _chunk1 _chunk_size)
	  (add_guard _jst (* (+ _chunk1 1) _chunk_size))
	  (mul_guard (+ _chunk1 1) _chunk_size)
	  (add_guard _chunk1 1)
	  (add_guard _jst (* _chunk2 _chunk_size))
	  (mul_guard _chunk2 _chunk_size)
	  (add_guard _jst (* (+ _chunk2 1) _chunk_size))
	  (mul_guard (+ _chunk2 1) _chunk_size)
	  (add_guard _chunk2 1)
	  
	  ;chunk1 =/= chunk2,  
	  (not (= _chunk1 _chunk2))
	
	  ;chunk_size = ceil((jend-jst+1)/(nthreads-x)),  0 <= x < nthreads
	  (= _chunk_size (ceil (+ (- _jend _jst) 1) (- _nthreads _x)))  
	  (<= 0 _x)
	  (< _x _nthreads)
	  (ceil_guard (+ (- _jend _jst) 1) (- _nthreads _x)) 
	  (add_guard (- _jend _jst) 1) 
	  (sub_guard _jend _jst) 
	  (sub_guard _nthreads _x) 
	  
	  ;if (schedule.kind == static) 
	  ;	chunkSize*(numThreads*n+t1)+1 <= chunk1 <= chunkSize*(numThreads*n+t1+1), 
	  ;	chunkSize*(numThreads*n+t2)+1 <= chunk2 <= chunkSize*(numThreads*n+t2+1),
	  ;	0 <= n, t1 =/= t2, 0 <= t1, t2 < numThreads
	  (...)
	  (not (= _t1 _t2))
	  (<= 0 _t1)(< _t1 _nthreads)
	  (<= 0 _t2)(< _t2 _nthreads) 
	))
	 *
	 * @param loop
	 * @return
	 */
	private Proposition getLoopGeneralAssertion(IASTForStatement loop) {
		assert peekCondition() != null && loop != null;
		
		// andIteratorsOf(loop);
//		  TODO:(<= MIN _x)         (<= _x MAX)
//		  (<= MIN _j1)        (<= _j1 MAX)
//		  (<= MIN _j2)        (<= _j2 MAX)
		final ASTAddressable da = cacheRuntimeAddress();
		final VODCondGen cg = getCondGen();
		final ThreadPrivateVersion<PathVariable> i1 = getThreadIteratorOf(loop, ThreadRole.THREAD1),
				i2 = getThreadIteratorOf(loop, ThreadRole.THREAD2);
		final ParallelCondition cond = peekCondition();
		final VariablePlaceholder<?> c1 = cond.getThreadChunk(ThreadRole.THREAD1),	// chunk1
				c2 = cond.getThreadChunk(ThreadRole.THREAD2),	// chunk2
				t1 = cond.getThread(ThreadRole.THREAD1),		// thread1
				t2 = cond.getThread(ThreadRole.THREAD2),		// thread2
				cs = cond.getChunkSize(), 
				x = cond.getThread(null), nts = cond.getNumThreads();
//		privatize(i1.getSubject(), false);
//		privatize(c1.getName(), false);
//		privatize(t1.getName(), false);
		cond.andIntVariable(i1);
		cond.andIntVariable(i2);
		
		// andBoundsOf(loop);
//		  (<= MIN _jst)       (<= _jst MAX)
//		  (<= MIN _jend)      (<= _jend MAX)
		ArithmeticExpression lb = ArithmeticExpression.fromLowerBoundOf(loop, da, cg);
		if (lb instanceof VariablePlaceholder) cond.andIntVariable((VariablePlaceholder<?>) lb);
		ArithmeticExpression ub = ArithmeticExpression.fromUpperBoundOf(loop, da, cg);
		if (ub instanceof VariablePlaceholder) cond.andIntVariable((VariablePlaceholder<?>) ub);
		
		// TODO: when collapse > 0...
//		  ;jst+chunk1*chunk_size <= j1 < jst+(chunk1+1)*chunk_size,  jst+chunk2*chunk_size <= j2 < jst+(chunk2+1)*chunk_size, 
		Proposition ass = null;
		if (lb instanceof Arithmetic && ub instanceof Arithmetic) {
			Arithmetic lba = (Arithmetic) lb, uba = (Arithmetic) ub;
			
//		  (<= (+ _jst (* _chunk1 _chunk_size)) _j1)(< _j1 (+ _jst (* (+ _chunk1 1) _chunk_size)))
			ass = lba.add(c1.multiply(cs)).lessEqual(i1);
			ass = ass.and(()-> i1.lessThan(lba.add(c1.add(Int.ONE).multiply(cs))));
			
//		  (<= (+ _jst (* _chunk2 _chunk_size)) _j2)(< _j2 (+ _jst (* (+ _chunk2 1) _chunk_size)))
			ass = ass.and(()-> lba.add(c2.multiply(cs)).lessEqual(i2));
			ass = ass.and(()-> i2.lessThan(lba.add(c2.add(Int.ONE).multiply(cs))));
			
//			  ;chunk_size = ceil((jend-jst+1)/(nthreads-x)),  0 <= x < nthreads
//			  (= _chunk_size (ceil (/ (+ (- _jend _jst) 1) (- _nthreads _x))))  
//			  (add_guard _jst (* _chunk1 _chunk_size))
//			  (mul_guard _chunk1 _chunk_size)
//			  (add_guard _jst (* (+ _chunk1 1) _chunk_size))
//			  (mul_guard (+ _chunk1 1) _chunk_size)
//			  (add_guard _chunk1 1)
//			  (add_guard _jst (* _chunk2 _chunk_size))
//			  (mul_guard _chunk2 _chunk_size)
//			  (add_guard _jst (* (+ _chunk2 1) _chunk_size))
//			  (mul_guard (+ _chunk2 1) _chunk_size)
//			  (add_guard _chunk2 1)
//			  
//			  (ceil_guard (+ (- _jend _jst) 1) (- _nthreads _x)) 
//			  (add_guard (- _jend _jst) 1) 
//			  (sub_guard _jend _jst) 
//			  (sub_guard _nthreads _x) 
			final ArithmeticExpression ceilArg = uba.subtract(lba).add(Int.ONE).divide(nts.subtract(x));
			ass = ass.and(()-> 
			Equality.from(cs, cg.getCeilFunction().getCall(Arrays.asList(ceilArg), cond)));
//			result = result.and(()->
//			cg.getCeilGuardFunction().getCall(ceilArg, condition).getCallProposition());
		}
		
		/*
	  ;if (schedule.kind == static) 
	  (...)
		 */
		if (schedule == OmpUtil.Schedule.STATIC) {
//			;	0 <= n1, 0 <= n2, 
			final VariablePlaceholder<?> n1 = cond.getThreadRound(ThreadRole.THREAD1),	// n1
					n2 = cond.getThreadRound(ThreadRole.THREAD2);						// n2
			ass = And.fromSkipNull(ass, ()-> Int.ZERO.lessEqual(n1));
			ass = ass.and(()-> Int.ZERO.lessEqual(n2));
			
//			;	chunkSize*(numThreads*n1+t1)+1 <= chunk1 <= chunkSize*(numThreads*n1+t1+1),
			ArithmeticExpression coeBase1 = nts.multiply(n1);	// numThreads*n1
			ass = ass.and(()-> cs.multiply(coeBase1.add(t1)).add(Int.ONE).lessEqual(c1));
			ass = ass.and(()-> c1.lessEqual(cs.multiply(coeBase1.add(t1).add(Int.ONE))));
			
//			;	chunkSize*(numThreads*n2+t2)+1 <= chunk2 <= chunkSize*(numThreads*n2+t2+1),
			ArithmeticExpression coeBase2 = nts.multiply(n2);	// numThreads*n2
			ass = ass.and(()-> cs.multiply(coeBase2.add(t2)).add(Int.ONE).lessEqual(c2));
			ass = ass.and(()-> c2.lessEqual(cs.multiply(coeBase2.add(t2).add(Int.ONE))));
		}

		return ass;
	}
	
	/**
	 * Two-threads interaction should be capable representing all numbers of threads.
	 * 
	 * @param loop
	 * @param role
	 * @return
	 * @throws NoSuchVersionException 
	 */
	@SuppressWarnings("unchecked")
	private ThreadPrivateVersion<PathVariable> getThreadIteratorOf(
			IASTForStatement loop, FunctionallableRole role) {
		assert loop != null && role != null;
		try {
			return ThreadPrivateVersion.from(
					(Assignable<PathVariable>) Assignable.fromCanonicalIteratorOf(loop, cacheRuntimeAddress(), getCondGen()),
					loop, 
					role);
			
		} catch (NoSuchVersionException e) {
			return throwTodoException("non-initialized iterator", e);
		}
	}
	

	
	public int getCollapse() {
		assert collapse.size() >= 1;
		return collapse.size();
	}
	
	public IASTForStatement getForStatement() {
		return (IASTForStatement) getStatement();
	}

	public Schedule getSchedule() {
		return schedule;
	}
	
	/**
	 * @param schedule
	 */
	private void setSchedule(Schedule schedule) {
		this.schedule = schedule;
	}
	
}
