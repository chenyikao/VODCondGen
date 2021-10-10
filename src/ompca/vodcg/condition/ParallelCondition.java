package ompca.vodcg.condition;

import java.util.Collections;
import java.util.Map;
import java.util.HashMap;
import java.util.HashSet;
import java.util.NavigableSet;
import java.util.Set;
import java.util.function.Supplier;

import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.Addressable;
import ompca.condition.SerialFormat;
import ompca.vodcg.ASTAddressable;
import ompca.vodcg.ASTUtil;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.data.DataType;
import ompca.vodcg.condition.data.FiniteNumberGuard;
import ompca.vodcg.condition.data.Int;
import ompca.vodcg.condition.version.ThreadRole;
import ompca.vodcg.condition.version.Version;
import ompca.vodcg.parallel.OmpDirective;
import ompca.vodcg.parallel.OmpReduceable;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class ParallelCondition extends Condition implements Addressable {

	static private final Map<IASTStatement, ParallelCondition> COND_CACHE = new HashMap<>();
	
	private VariablePlaceholder<?> numThreads = null;	// nthreads
	private VariablePlaceholder<?> chunkSize = null;	// _chunk_size
	private VariablePlaceholder<?> thread = null;		// x
	private VariablePlaceholder<?> thread1 = null;		// _t1
	private VariablePlaceholder<?> thread2 = null;		// _t2
	private VariablePlaceholder<?> thread1Round = null;	// _n1
	private VariablePlaceholder<?> thread2Round = null;	// _n2
	private VariablePlaceholder<?> thread1Chunk = null;	// _chunk1
	private VariablePlaceholder<?> thread2Chunk = null;	// _chunk2

	private NavigableSet<OmpDirective> dirs;
	private IASTStatement stat;
	


	public static ParallelCondition from(IASTStatement stat, final ASTAddressable rtAddr, VODCondGen condGen) {
		if (stat == null) throwNullArgumentException("stat");
		
		ParallelCondition pc = COND_CACHE.get(stat);
		if (pc == null) COND_CACHE.put(stat, pc = new ParallelCondition(stat, rtAddr, condGen));
		return pc;
	}
	
	/**
	 * @param stat
	 * @param rtAddr - some run-time address determined by an OpenMP directive for example
	 * @param condGen
	 */
	private ParallelCondition(IASTStatement stat, final ASTAddressable rtAddr, VODCondGen condGen) {
		super(rtAddr, condGen);
		
		assert stat != null;
		this.stat = stat;
		final String addr = "_" + getShortAddress();
		
//		  (<= 1 _nthreads)  (<= _nthreads MAX)
		andPositiveIntVariable(numThreads = VariablePlaceholder.fromNonAST(
				Variable.fromNonAST("_nthreads", DataType.Int, false, ()-> this, stat, condGen),
				true));
//				TODO? Variable.getNonAST("nthreads" + addr, DataType.Int, null, cg)));
		
//		  (<= 1 _chunk_size)(<= _chunk_size MAX)
		andPositiveIntVariable(chunkSize = VariablePlaceholder.fromNonAST(
				Variable.fromNonAST("_chunk_size" + addr, DataType.Int, false, ()-> this, stat, condGen),
				true));
		
		Variable t = Variable.fromNonAST("_t" + addr, DataType.Int, false, ()-> this, stat, condGen),
				chunk = Variable.fromNonAST("_chunk" + addr, DataType.Int, false, ()-> this, stat, condGen),
				round = Variable.fromNonAST("_round" + addr, DataType.Int, false, ()-> this, stat, condGen);
//		  ;chunk_size = ceil((jend-jst+1)/(nthreads-x)),  0 <= x < nthreads
		andNonNegativeIntVariable(
				thread = VariablePlaceholder.getThreadPrivate(t, stat, ThreadRole.FUNCTION, true, true, null));
//		  (<= 0 _x)
//		  (< _x _nthreads)
		and(()-> Int.ZERO.lessEqual(thread));
		and(()-> thread.lessThan(numThreads));
		
//		  (<= 0 _chunk1)    (<= _chunk1 MAX)
		andNonNegativeIntVariable(
				thread1 = VariablePlaceholder.getThreadPrivate(t, stat, ThreadRole.THREAD1, true, true, null));
		andNonNegativeIntVariable(
				thread1Chunk = VariablePlaceholder.getThreadPrivate(chunk, stat, ThreadRole.THREAD1, true, true, null));
		andNonNegativeIntVariable(
				thread1Round = VariablePlaceholder.getThreadPrivate(round, stat, ThreadRole.THREAD1, true, true, null));
		
//		  (<= 0 _chunk2)    (<= _chunk2 MAX)
		andNonNegativeIntVariable(
				thread2 = VariablePlaceholder.getThreadPrivate(t, stat, ThreadRole.THREAD2, true, true, null));
		andNonNegativeIntVariable(
				thread2Chunk = VariablePlaceholder.getThreadPrivate(chunk, stat, ThreadRole.THREAD2, true, true, null));
		andNonNegativeIntVariable(
				thread2Round = VariablePlaceholder.getThreadPrivate(round, stat, ThreadRole.THREAD2, true, true, null));
		
//		andGeneral();
//		  ;chunk1 =/= chunk2,  
//		  (not (= _chunk1 _chunk2))
		and(()-> thread1Chunk.equal(thread2Chunk).not());
//		  ;	t1 =/= t2, 0 <= t1, t2 < numThreads
//		  (not (= _t1 _t2))
		and(()-> thread1.equal(thread2).not());
//		  (<= 0 _t1)(< _t1 _nthreads)
		and(()-> Int.ZERO.lessEqual(thread1));
		and(()-> thread1.lessThan(numThreads));
//		  (<= 0 _t2)(< _t2 _nthreads) 
		and(()-> Int.ZERO.lessEqual(thread2));
		and(()-> thread2.lessThan(numThreads));
	}

	@Override
	protected Object cloneNonConstant() {
		ParallelCondition clone = (ParallelCondition) super.cloneNonConstant();
		clone.numThreads = numThreads;
		clone.chunkSize = chunkSize;
		clone.thread = thread;
		clone.thread1 = thread1;
		clone.thread2 = thread2;
		clone.thread1Chunk = thread1Chunk;
		clone.thread2Chunk = thread2Chunk;
		clone.dirs = dirs;
		clone.stat = stat;
		return clone;
	}

	
	
	@Override
	public String getIDSuffix(SerialFormat format) {
		return Addressable.super.getIDSuffix(format);
	}
	
	/* (non-Javadoc)
	 * @see ompca.vodcg.condition.Addressable#getShortAddress()
	 */
	@Override
	public String getShortAddress() {
		return ASTUtil.toLineLocationOf(stat.getFileLocation());
	}


	
	public VariablePlaceholder<?> getNumThreads() {
		return numThreads;
	}
	
	public VariablePlaceholder<?> getChunkSize() {
		return chunkSize;
	}
	
	public VariablePlaceholder<?> getThread(ThreadRole role) {
		if (role == null) return thread;
		
		switch (role) {
		case MASTER:
		case NON_MASTER:
		case FUNCTION:	return thread;
		case THREAD1:	return thread1;
		case THREAD2:	return thread2;
		default:
		}
		return throwTodoException("unsupported role");
	}
	
	public VariablePlaceholder<?> getThreadChunk(ThreadRole role) {
		if (role != null) switch (role) {
		case THREAD1:	return thread1Chunk;
		case THREAD2:	return thread2Chunk;
		default:
		}
		return throwTodoException("unsupported role");
	}
	
	public VariablePlaceholder<?> getThreadRound(ThreadRole role) {
		if (role != null) switch (role) {
		case THREAD1:	return thread1Round;
		case THREAD2:	return thread2Round;
		default:
		}
		return throwTodoException("unsupported role");
	}
	
	/**
	 * @param vName - name of the non-AST variable
	 * @return
	 */
	public VariablePlaceholder<?> getIntVariable(
			String vName, IASTStatement vAstScope) {
		if (vName == null) return null;
		
		final VariablePlaceholder<?> v = VariablePlaceholder.fromNonAST(
				Variable.fromNonAST(vName, DataType.Int, false, ()-> this, vAstScope, getCondGen()),
				true);
		andIntVariable(v);
		return v;
	}
	
	@SuppressWarnings("unchecked")
	@Override
	protected <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType) {
		if (refType == null) return throwNullArgumentException("reference type", ()-> Collections.emptySet());
		
		final Set<T> dvrs = new HashSet<>(super.cacheDirectVariableReferences(refType));
		try {
		if (refType.equals(VariablePlaceholder.class)) {
			dvrs.add((T) numThreads);
			dvrs.add((T) chunkSize);
			dvrs.add((T) thread);
			dvrs.add((T) thread1);
			dvrs.add((T) thread2);
			dvrs.add((T) thread1Chunk);
			dvrs.add((T) thread2Chunk);
			
		} else if (refType.asSubclass(Version.class) != null) { // throws ClassCastException if not Version
			dvrs.add((T) numThreads.getVersion());
			dvrs.add((T) chunkSize.getVersion());
			dvrs.add((T) thread.getVersion());
			dvrs.add((T) thread1.getVersion());
			dvrs.add((T) thread2.getVersion());
			dvrs.add((T) thread1Chunk.getVersion());
			dvrs.add((T) thread2Chunk.getVersion());
			
		}	// refType == PathVariablePlaceholder...
		} catch (ClassCastException e) {
			if (!refType.equals(PathVariablePlaceholder.class)) throwTodoException(e);
		}
		return dvrs;
	}
	
	
	
	/**
	 * @return non-null
	 */
	public NavigableSet<OmpDirective> getDirectives() {
		if (dirs == null) dirs = OmpDirective.from(stat, getCondGen());
		return dirs != null
				? dirs
				: Collections.emptyNavigableSet();
	}
	
	public boolean addDirective(OmpDirective dir) {
		return getDirectives().add(dir);
	}
	
//	public void setDirectives(List<OmpDirective> newDirs) {
//		dirs.clear();
//		dirs.addAll(newDirs);
////		and(dir.generateAssertion());
//	}

	

	public void and(Set<VODConditions> conds) {
		if (conds == null) throwNullArgumentException("conditions");
		for (VODConditions cond : conds) and(cond);
	}
	
	public void and(VODConditions conds) {
		if (conds == null) throwNullArgumentException("conditions");
		andNonNull(conds.getParallelCondition());
//		andNonNull(conds.getPathCondition());
	}
	
	public void and(ParallelCondition cond2) {
		if (cond2 == null) throwNullArgumentException("condition");
//		if (!equalsAddress(cond2)) Debug.throwInvalidityException("different variables");
		
		if (equalsAddress(cond2)) super.and(cond2);
	}
	
	/**
	 * Adding parallel region reduction condition.
	 * 
	 * @param dir - a reduce-able directive with parallel region
	 */
	public void and(OmpReduceable dir) {
		if (dir != null && dir.reducesAny()) and(()-> dir.generateReductionAssertion());
//		throwTodoException("unsupported operation");
	}
	
	public Supplier<Proposition> andIntVariable(VariablePlaceholder<?> vp) {
		if (vp == null) throwNullArgumentException("variable placeholder");
		
		vp.fillScope(this);
		andNonNull(vp.getSideEffect());
		return getAssertion();
	}
	
	public Supplier<Proposition> andIntVariable(Version<? extends Variable> ver) {
		if (ver == null) throwNullArgumentException("version");
		
		ver.fillScope(this);
		andNonNull(ver.getSideEffect());
		return getAssertion();
	}
	
	public Supplier<Proposition> andIntVariable(Variable v) {
		if (v == null) return null;
		return andIntVariable(VariablePlaceholder.fromNonAST(v, true));
	}
	
	/**
	 * @param vName - name of the non-AST variable
	 * @return
	 */
	public Supplier<Proposition> andIntVariable(
			String vName, IASTStatement vAstScope) {
		if (vName == null) return null;
		return andIntVariable(VariablePlaceholder.fromNonAST(
				Variable.fromNonAST(vName, DataType.Int, false, null, vAstScope, getCondGen()),
				vAstScope == null));
	}
	
	public Supplier<Proposition> andPositiveIntVariable(VariablePlaceholder<?> vp) {
		if (vp == null) throwNullArgumentException("variable placeholder");
		vp.addGuard(FiniteNumberGuard.fromPositive(vp));
		return andIntVariable(vp);
	}
	
	public Supplier<Proposition> andNonNegativeIntVariable(VariablePlaceholder<?> vp) {
		if (vp == null) throwNullArgumentException("variable placeholder");
		vp.addGuard(FiniteNumberGuard.fromNonNegative(vp));
		return andIntVariable(vp);
	}
	
	/**
	 * @param cond
	 */
	private void andNonNull(Condition cond) {
		if (cond != null) and(cond);
	}
	
	/**
	 * @param conds
	 */
	private void andNonNull(VODConditions conds) {
		if (conds != null) and(conds);
	}
	
	
	
	/**
	 * @return Disjunction of sub-directive race conditions.
	 */
	public Proposition generateRaceAssertion() {
		Proposition result = null;
		for (OmpDirective dir : getDirectives()) {
			Proposition dirRace = dir.generateRaceAssertion();
			if (result == null) result = dirRace;
			else if (dirRace != null) result = result.or(()-> dirRace);
		}
		return result;
	}



	/* (non-Javadoc)
	 * @see ompca.vodcg.condition.Addressable#previous()
	 */
	@SuppressWarnings("unchecked")
	@Override
	public ParallelCondition previous() {
		return throwTodoException("previous parallel condition");
	}
	


//	@Override
//	public boolean equalsAddress(Addressable a2) {
//		if (a2 == null) Debug.throwInvalidityException("null a2");
//		if (!(a2 instanceof ParallelCondition)) return false;
//		
//		ParallelCondition cond2 = (ParallelCondition) a2;
//		return !numThreads.equals(cond2.numThreads) || !chunkSize.equals(cond2.chunkSize) ||
//				!thread1.equals(cond2.thread1) || !thread2.equals(cond2.thread2) ||
//				!thread1Chunk.equals(cond2.thread1Chunk) || 
//				!thread2Chunk.equals(cond2.thread2Chunk) ||
//				!thread.equals(cond2.thread);
//	}
	
	protected <T extends SideEffectElement> boolean suitsSideEffect(T newSe) {
		final boolean ss = super.suitsSideEffect(newSe);
		if (!(newSe instanceof ParallelCondition)) return ss;
		
		return ss && equalsAddress((ParallelCondition) newSe);
	}

}