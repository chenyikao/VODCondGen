/**
 * 
 */
package ompca.vodcg.parallel;

import java.util.regex.Pattern;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.NavigableSet;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.regex.Matcher;

import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.ListValueMap;
import ompca.vodcg.ASTUtil;
import ompca.vodcg.Assignable;
import ompca.vodcg.Assignment;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.Equality;
import ompca.vodcg.condition.FunctionalPathVariable;
import ompca.vodcg.condition.ParallelCondition;
import ompca.vodcg.condition.PathVariable;
import ompca.vodcg.condition.PathVariablePlaceholder;
import ompca.vodcg.condition.Proposition;
import ompca.vodcg.condition.data.NumericExpression;
import ompca.vodcg.condition.version.ArrayAccessVersion;
import ompca.vodcg.condition.version.FunctionalVersion;
import ompca.vodcg.condition.version.ThreadRole;
import ompca.vodcg.condition.version.Version;
import ompca.vodcg.condition.version.VersionPlaceholder;

/**
 * @author Kao, Chen-yi
 *
 */
public class OmpParallel extends OmpReduceable {

	private SortedSet<OmpDirective> dirs = null;
	
	

	private OmpParallel(IASTFileLocation address, IASTStatement blockStat, 
			ParallelCondition pc, final SortedSet<OmpDirective> dirs, VODCondGen condGen) {
		super(null, address, blockStat, false, pc, condGen);
		
		this.dirs = dirs == null ? new TreeSet<>(this) : new TreeSet<>(dirs);
		pc.and(this);
	}
	
	public static OmpParallel from(IASTNode node, VODCondGen condGen) {
		if (node == null) return null;
		
//		OmpParallel p = PARALLEL_REGION_CACHE.get(stat);
//		if (p != null) return p;
		
		final NavigableSet<OmpDirective> ds = OmpDirective.fromReversedly(
				ASTUtil.getAncestorOfAs(node, ASTUtil.AST_STATEMENT_TYPE, true), condGen);
		if (ds == null) return null;
		
//		PARALLEL_REGION_CACHE.put(stat, p);
		OmpParallel p = null;
		for (OmpDirective d : ds) {
			p = d.getParallelRegion();
			if (p != null) return p;
		}
		return p;
	}
	
	protected static OmpParallel from(String clauses, IASTFileLocation address, 
			IASTStatement blockStat, ParallelCondition pc, final SortedSet<OmpDirective> dirs, VODCondGen condGen) {
		assert address != null;
		
		Matcher mParallel = Pattern.compile("(?<for>for)?"	 									+ "("
				+ OmpUtil.patternIf("if", "scalar_expression") 									+ "|" 
				+ OmpUtil.patternPrivate("private", "privateList", null, null)					+ "|" 
				+ OmpUtil.patternShared("shared", "sharedList", null, null)						+ "|" 
				+ OmpUtil.patternDefault("default", "defaultShared", "defaultNone") 			+ "|" 
				+ OmpUtil.patternFirstPrivate("firstprivate", "firstPrivateList", null, null)	+ "|" 
				+ OmpUtil.patternReduction("reduction", "operator", "reductionList", null, null)+ "|" 
				+ OmpUtil.patternCopyIn("copyIn", "copyInList", null, null)						+ "|" 
				+ OmpUtil.patternNumThreads("numThreads", "integer-expression")					+ "|" 
				+ "\\s" + ")*").matcher(clauses);

		// asssert exists 'omp parallel ' + clauses
		OmpParallel op = new OmpParallel(address, blockStat, pc, dirs, condGen);

		while (mParallel.find()) {
			final String clausePrivate = mParallel.group("private"),
					clauseFirstPrivate = mParallel.group("firstprivate"),
					clauseCopyIn = mParallel.group("copyIn"),
					clauseShared = mParallel.group("shared"),
					clauseReduction = mParallel.group("reduction");
			if (mParallel.group("for") != null && blockStat instanceof IASTForStatement) 
				op.wrap(OmpFor.from(op, null, false, clausePrivate, clauseFirstPrivate, clauseCopyIn, 
						clauseShared, clauseReduction, false, 
						address, (IASTForStatement) blockStat, pc, condGen)); 
			if (clausePrivate != null) 
				op.parseAndPrivatize(mParallel.group("privateList"));
			if (clauseShared != null);		// TODO, "sharedList") != null);
			if (mParallel.group("default") != null);	// variables are default shared already, TODO, "defaultNone") != null);
			if (clauseFirstPrivate != null);	// TODO, "firstPrivateList") != null);
			if (clauseCopyIn != null);			// TODO
			if (clauseReduction != null);	// TODO: forall (i, n), thread_i_frc1_n = thread_i_frc1_n-1 + ..., 
			// "operator", "reductionList") != null);
		}
		// TODO: cache result!
		return op;
	}

	
	
	public boolean add(OmpFlushable dir) {
		if (dirs.contains(dir)) return false;
		if (!dirs.add(dir)) return throwTodoException("not addable directive");
		
		dir.setParallelRegion(this);
		return true;
	}
	
	/**
	 * @return non-null
	 */
	public SortedSet<OmpDirective> getDirectives() {
		for (IASTNode child : Arrays.asList(getStatement().getChildren()))
			if (child instanceof IASTStatement) 
				dirs.addAll(OmpDirective.from((IASTStatement) child, this, getCondGen()));
		return dirs;
	}
	
	@Override
	public OmpParallel getParallelRegion() {
		return this;
	}
	
	public OmpParallel getParent() {
		return from(getStatement().getParent(), getCondGen());
	}
	
	@Override
	public Set<PathVariablePlaceholder> getPrivatizedPlaceholders() {
		final Set<PathVariablePlaceholder> pps = 
				new HashSet<>(super.getPrivatizedPlaceholders());
		for (OmpDirective dir : dirs) 
			if (dir instanceof OmpThreadPrivatizable)
				pps.addAll(((OmpThreadPrivatizable) dir).getPrivatizedPlaceholders());
		return pps;
	}

	@Override
	public Set<PathVariablePlaceholder> getPrivatizedPlaceholders(
			PathVariable v) {
		final Set<PathVariablePlaceholder> pps = 
				new HashSet<>(super.getPrivatizedPlaceholders(v));
		for (OmpDirective dir : dirs) 
			if (dir instanceof OmpThreadPrivatizable)
				pps.addAll(((OmpThreadPrivatizable) dir).getPrivatizedPlaceholders(v));
		return pps;
	}

	@Override
	protected Set<PathVariablePlaceholder> getPrivatizedArrayEnclosers() {
		final Set<PathVariablePlaceholder> spaes = super.getPrivatizedArrayEnclosers(),
				paes = new HashSet<>(spaes);
		for (OmpDirective dir : dirs) {
			if (dir instanceof OmpFlushable) {
				final OmpFlushable flu = (OmpFlushable) dir;
				for (PathVariablePlaceholder spae : spaes) 
					paes.addAll(flu.getArrayEnclosersLike(spae));
				if (flu.isSynchronized()) break;
			} else
				throwTodoException("unsupported directive");
		}
		return paes;
	}
	
	/**
	 * Caching array-relative race condition.
	 * 
	 * @return Disjunction of sub-dirs race conditions and array read-write or write-write sub-races.
	 * 	Each sub-race indicates that for some parallel private variables i_1 and i_2 of
	 * 	different threads, array[i_1] = ... && array[i_2] = ... && (i_1 = i_2 => array[i_1] != array[i_2])
	 */
	@Override
	protected Proposition cacheRaceAssertion() {
		Proposition race = null;
		// sub-dirs race conditions
		for (OmpDirective dir : dirs) {
			final Proposition dirRace = dir.generateRaceAssertion();
			race = race == null ? dirRace : race.or(()-> dirRace);
		}

		// array sub-race conditions
		final Proposition arrayRace = generateArrayRaceAssertion();
		race = race == null ? arrayRace : race.or(()-> arrayRace);
		return race;
	}

	protected Proposition generateArrayRaceAssertion() {
		final ListValueMap<PathVariable, ArrayAccessVersion<?>> 
		wvs = new ListValueMap<>(), rvs = new ListValueMap<>();
		
		// non-argument private's writing doesn't cause race
		for (PathVariablePlaceholder pvpe : getPrivatizedArrayEnclosers()) try {
			final Assignable<?> easn = pvpe.getAssignable();
			@SuppressWarnings("unchecked")
			final ArrayAccessVersion<PathVariable> ev = (ArrayAccessVersion<PathVariable>) (tests(easn.isDirectlyFunctional())
					? FunctionalVersion.from((Assignable<PathVariable>) easn)
					: ArrayAccessVersion.from(
					(Version<PathVariable>) pvpe.getVersion(ArrayAccessVersion.class), 
					(Assignable<PathVariable>) easn, pvpe.getThreadRole()));
			final PathVariable v = ev.getSubject();
			if (tests(pvpe.isAssigned())) wvs.put(v, ev);
			else rvs.put(v, ev);
			
		} catch (Exception e) {
			throwTodoException(e);
		}
		
		Proposition race = null;
		for (PathVariable v : wvs.keySet()) {
//			int i = 1;
			final List<ArrayAccessVersion<?>> vwvs = wvs.get(v);
//			final int vwSize = vwvs.size();
			for (ArrayAccessVersion<?> wv : vwvs) {
				final IASTStatement pb = wv.getPrivatizingBlock();
				final Proposition asm = getNonNull(()-> wv.getAssignment().toEquality());
				// for example a[i11]=a[i11+1]+1 && a[i12]=a[i12+1]+1 && a[i2]=a[i2+1]+1  
				final Proposition asm11 = asm.cloneReversion(pb, ThreadRole.THREAD1.extend("1"), null),
						asm12 = asm.cloneReversion(pb, ThreadRole.THREAD1.extend("2"), null),
						asm2 = asm.cloneReversion(pb, ThreadRole.THREAD2, null),
						asmp = asm11.and(asm12).and(asm2);
				
				// read-write race
//				for (ArrayAccessVersion<?> rv : rvs.get(v)) {
//					final Proposition wrRace = asmp.and(()-> generateRaceAssertion(wv, rv));
//					race = race == null ? wrRace : race.or(wrRace);
//				}
				
				/* write-write race, for example,
				 *  
				 * a[i11]=a[i11+1]+1 && a[i12]=a[i12+1]+1 && a[i2]=a[i2+1]+1 
				 * && i11 == i12 && i11 != i2 && i12 != i2 && a[i11] != a[i12] given
				 * 
				 * #pragma omp parallel for
				 *   for (i=0;i< len -1 ;i++)
				 *       a[i]=a[i+1]+1;
				 */
				for (ArrayAccessVersion<?> wv2 : vwvs) if (wv == wv2) {
					final Proposition wwRace = asmp.and(()-> generateRaceAssertion(wv, wv2));
					race = race == null ? wwRace : race.or(wwRace);
				}
//				if (i < vwSize) 
//					for (ArrayAccessVersion<?> wv2 : vwvs.subList(i, vwSize)) {
//					}
//				i++;
			}
		}

		/* read-share race, for example, x is shared and assigned by private i:
		 *   int i,x;  
		 *   int len = 10000;
		 *   #pragma omp parallel for private (i)
		 *     for (i=0;i<len;i++)
		 *         x=i;
		 */
		for (PathVariable v : rvs.keySet()) {
			final List<ArrayAccessVersion<?>> vrvs = rvs.get(v);
			for (ArrayAccessVersion<?> rv : vrvs) {
				final Assignment asm = rv.getAssignment();
				if (asm == null) continue;
				
				final Proposition asmEq = getNonNull(()-> asm.toEquality());
				if (asmEq instanceof Equality) {
					final IASTStatement pb = rv.getPrivatizingBlock();
					if (((Equality) asmEq).getAssigned().isThreadPrivate()) continue;
					
					@SuppressWarnings("unchecked")
					final VersionPlaceholder<FunctionalPathVariable> rvp = (VersionPlaceholder<FunctionalPathVariable>) rv.getPlaceholder();
					final Proposition asm1 = asmEq.substitute(rvp, rv.cloneReversion(pb, ThreadRole.THREAD1, null)),
							asm2 = asmEq.substitute(rvp, rv.cloneReversion(pb, ThreadRole.THREAD2, null)),
							asmp = asm1.and(asm2);
					
					race = race == null ? asmp : race.or(asmp);
				}
			}
		}
		return race;
	}
	


	private Proposition generateRaceAssertion(
			ArrayAccessVersion<?> wv, ArrayAccessVersion<?> v2) {
		assert wv != null && v2 != null && wv.getSubject() == v2.getSubject();
		
		Proposition race = null, ite = null, ites = null;
		try {
			final OmpDirective dir1 = wv.getAssignable().getEnclosingDirectives().last(),
					dir2 = v2.getAssignable().getEnclosingDirectives().last();
			final Set<PathVariablePlaceholder> pps = getPrivatizedPlaceholders();

			if (dir1 == dir2) {
				for (IASTStatement loop : wv.getAssignable().getDependentLoops()) 
					if (loop instanceof IASTForStatement) {
						final IASTForStatement forLoop = (IASTForStatement) loop;
						final PathVariablePlaceholder it = Assignable.fromCanonicalIteratorOf(
								forLoop, getRuntimeAddress(), getCondGen()).getPathVariablePlaceholder();
						if (!pps.contains(it)) continue;
						
						ite = ((NumericExpression) it.cloneReversion(loop, ThreadRole.THREAD1.enumerate("1"), null))
								.equal(it.cloneReversion(loop, ThreadRole.THREAD1.enumerate("2"), null));
						ites = ites == null ? ite : ites.and(ites);
					} else 
						throwTodoException("unsupported loop");
				
				// exists i11 == i12 && j11 == j12 && i11 != i2 && i12 != i2 && j1 != j2 && ... && array[i11, j11, ...] != array[i12, j12, ...]
				race = ites.and(()-> ((NumericExpression) wv.cloneReversion(null, ThreadRole.THREAD1.enumerate("1"), null))
								.equal(v2.cloneReversion(null, ThreadRole.THREAD1.enumerate("2"), null)).not()); 
//					final List<ArithmeticExpression> args2 = v2.getAstArguments();
//					for (ArithmeticExpression ai1 : wv.getAstArguments()) {
//						final int i_ = i;
//						final Proposition argRace = ThreadPrivateVersion.fromThread1(ai1, loop)
//								.equal(ThreadPrivateVersion.fromThread2(args2.get(i_), loop)); 
//						race = race == null ? argRace : race.and(argRace);
//						i++;
//					}
			} else {
				if (dir1 instanceof OmpFlushable && !((OmpFlushable) dir1).isSynchronized() && dir2 instanceof OmpSingle) {
					/*
					 * For the case of 'nowait-then-single':
					 * array[i1_dir1] = ... && array[i_dir2] && i1_dir1 != i_dir2 && nowait_dir1 && single_dir2 
					 * => array[i2_dir1] = ... && i2_dir1 == i_dir2 && array[i_dir2] != array[i2_dir1]
					 *  
					 * Ex. t1:{a[i1] = b + a[i1]*5 && i1 != 9 && error = a[9] + 1} 
					 * => t2:{a[i2] = b + a[i2]*5 && i2 == 9} && t1:{a[9]} != t2:{a[i2]} in 
					 * <pre>
					 * #pragma omp parallel shared(b, error)
					 * {
					 * #pragma omp for nowait
					 * 	for(i = 0; i < len; i++)
					 * 		a[i] = b + a[i]*5;
					 * 
					 * #pragma omp single
					 * 	error = a[9] + 1;
					 * }
					 * </pre>
					 */
					int i = 0;
					final int size = wv.getAstArguments().size();
					for (ArithmeticExpression wvArg = wv.getAstArgument(i); i < size; i++) if (wvArg != null)
						for (PathVariablePlaceholder pp : pps) if (wvArg.contains(pp)) {
							// array[i1_dir1] = ... && array[i_dir2] && i1_dir1 != i_dir2 
							// => array[i2_dir1] = ... && i2_dir1 == i_dir2 && array[i_dir2] != array[i2_dir1]
							final ArithmeticExpression i1Dir1 = wvArg.cloneReversion(null, ThreadRole.THREAD1, null),
									i2Dir1 = wvArg.cloneReversion(null, ThreadRole.THREAD2, null),
									iDir2 = v2.getAstArgument(i);
							final Proposition wvRace = i1Dir1.equal(iDir2).not().imply(()-> 
							i2Dir1.equal(iDir2).and(v2.equal(wv.cloneReindex(wvArg, i2Dir1)).not()));
							race = race == null ? wvRace : race.and(wvRace);
						}
					
				} else throwTodoException("unsupported array race");
			}
		} catch (Exception e) {
			throwTodoException(e);
		}
		return race;
	}

	
	
	@Override
	public Proposition generateReductionAssertion() {
		Proposition red = super.generateReductionAssertion();
		for (OmpDirective dir : dirs) if (dir instanceof OmpReduceable) {
			final Proposition loopRace = ((OmpReduceable) dir).generateReductionAssertion();
			red = red == null ? loopRace : red.or(()-> loopRace);
		}
		return red;
	}
	
	@Override
	public void reduce(String clause, final List<ArithmeticExpression> privateArgv) {
		super.reduce(clause, privateArgv);
		for (OmpDirective dir : dirs) 
			if (dir instanceof OmpReduceable) 
				((OmpReduceable) dir).reduce(clause, privateArgv);
	}

	/**
	 * @param dirs
	 */
	public void wrap(OmpFor loop) {
		add(loop);
		getCondition().and(loop);
	}

//	public boolean wrapsLoop() {
//		return dirs != null;
//	}
	
//	public OmpFor toLoop() {
//		return dirs;
//	}
	
}
