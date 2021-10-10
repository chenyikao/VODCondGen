package ompca.vodcg.condition.version;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.NavigableSet;
import java.util.Set;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;

import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.Pair;
import ompca.condition.SerialFormat;
import ompca.vodcg.ASTAddressable;
import ompca.vodcg.ASTException;
import ompca.vodcg.ASTLoopUtil;
import ompca.vodcg.ASTRuntimeLocationComputer;
import ompca.vodcg.ASTUtil;
import ompca.vodcg.Assignable;
import ompca.vodcg.FunctionalAssignable;
import ompca.vodcg.IncomparableException;
import ompca.vodcg.SystemElement;
import ompca.vodcg.UncertainPlaceholderException;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.ConditionElement;
import ompca.vodcg.condition.Equality;
import ompca.vodcg.condition.Expression;
import ompca.vodcg.condition.ExpressionRange;
import ompca.vodcg.condition.Forall;
import ompca.vodcg.condition.Function;
import ompca.vodcg.condition.Function.Parameter;
import ompca.vodcg.condition.FunctionCall;
import ompca.vodcg.condition.FunctionalPathVariable;
import ompca.vodcg.condition.InductiveType;
import ompca.vodcg.condition.PathVariable;
import ompca.vodcg.condition.PathVariablePlaceholder;
import ompca.vodcg.condition.Proposition;
import ompca.vodcg.condition.Variable;
import ompca.vodcg.condition.VariablePlaceholder;
import ompca.vodcg.condition.data.ArrayPointer;
import ompca.vodcg.condition.data.DataType;
import ompca.vodcg.condition.data.Int;
import ompca.vodcg.condition.data.PlatformType;
import ompca.vodcg.condition.data.PointerType;
import ompca.vodcg.condition.version.ThreadRole.ExtendedRole;
import ompca.vodcg.parallel.OmpDirective;

/**<pre>
 * A functional version represents any value of a functional path variable, which includes
 * any functionally value-changing loop iterator used as an array argument. Hence it's 
 * partially extending {@link ArrayAccessVersion}.
 * 
 * For an array path variable, its functional version is a trinity version type consisting of 
 * an initial, a closure and a post version of an inductive function.
 * 
 * E.g.:
 *  exists j, i, 
 * 	(j <= jbeg && i <= ibeg) => frc1(j, i) = 0.0                                     	(init.),
 * 	(jbeg < j < jfin1 && ibeg < i < ifin1) ��� 
 * 		frc1(j, i) = frc1(j-1, i-1) + ( phi1[j][i] + phi1[j][i+1] + phi1[j+1][i] + phi1[j+1][i+1] 
 * 					+ phi2[j][i] + phi2[j][i+1] + phi2[j+1][i] + phi2[j+1][i+1] )   (clos.),
 * 	(jfin1 � j && ifin1 � i) ��� 
 * 		frc1(j, i) = dxi * deta * frc1(jfin1-1, ifin1-1)             				(post)
 * 
 * A functional version is crossing-loop ubiquitous. Therefore an enumerated 
 * functional version f_enum[i][j] is still ubiquitous as f[i][j] is, however 
 * they are ubiquitous in different (enumerated and pseudo-universal) subversion levels.
 * </pre>
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class FunctionalVersion extends ArrayAccessVersion<FunctionalPathVariable> 
implements UbiquitousVersion<FunctionalPathVariable> {

	/**
	 * Functional loop indexes = (in-loop index, upper-bound index)
	 */
	final static private Map<IASTStatement, ArithmeticExpression[]> 
	LOOP_INDEXES 				= new HashMap<>();
	

	
//	/**
//	 * TODO? replacing by {@link PathVariablePlaceholder}
//	 */
//	private Assignable asn;
	
	/**
	 * Representing inductive function calls in recursion closures, ex. frc1(j, i) in 
	 * frc1(j, i) = frc1(j-1, i-1) + ...
	 */
	private FunctionCall<?> funcCallView 		= null;
//	/**
//	 * delaying {@link #getArguments} to avoid circular execution dependency
//	 */
//	private Runnable fcvSetter = null;
	
//	private List<ArithmeticExpression> astArgs;
	/**<pre>
	 * A loop argument has an AST loop statement key and two value elements, which are:
	 * 
	 * 1) loop index expression - representing the inductive parallel iteration schedule indexes 
	 * in recursive closure of functional array accesses, 
	 * ex. j-1 for loop j or i-1 for loop i in frc1(j, i) = frc1(j-1, i-1) + ...
	 * 
	 * 2) loop-dependent <em>sequential</em> enumerator expression for self assignment - 
	 * 
	 * for example, a[i][j] += a[i + 1][j] within loop j can be re-wrote to 
	 * 	a(i, j, loop_enumer(i,j) + 1) = a(i, j, loop_enumer(i,j)) + a(i + 1, j, loop_enumer(i,j)) 
	 * 	&& (i2 = i && j2 = j) -> loop_enumer(i2,j2) > loop_enumer(i,j) + 1, 
	 * where loop_enumer(i,j) is the enumerator for loop j.
	 * 
	 * Or for an indirect (functional) self assignment example:
	 *   for (i =0; i< N; ++i) {
	 *     int idx = indexSet[i];
	 *     xa1[idx]+= 1.0 + i;
	 *   }
	 *   => xa1[idx]+= 1.0 + i => xa1[indexSet[i]]+= 1.0 + i 
	 *   => xa1(indexSet[i], loop_enumer(i) + 1) = xa1(indexSet[i], loop_enumer(i)) + 1.0 + i
	 *   	&& (i2 > i && indexSet[i2] = indexSet[i] -> loop_enumer(i2) > loop_enumer(i) + 1),
	 * where loop_enumer(i) is the enumerator for loop i.
	 */
	private SortedMap<IASTStatement, Pair<ArithmeticExpression, ArithmeticExpression>> LoopArgs;
	/**
	 * delaying {@link #computeIndexOf} to avoid circular execution dependency
	 */
	private Runnable argSetter = null;

	final private List<ExpressionRange<? extends Expression>> argRanges = new ArrayList<>();
//	private Map<LValue, FunctionalVersion> initials 	= new HashMap<>();
//	private Map<LValue, FunctionalVersion> closures 	= new HashMap<>();
//	private Map<LValue, FunctionalVersion> posts 		= new HashMap<>();

	/**
	 * @param address
	 * @param subject
	 * @param role - the argument role for matching in {@link #setArguments(List)}
	 * @param astArgs
	 * @param loops
	 * @throws NoSuchVersionException
	 */
	private FunctionalVersion(final VersionEnumerable<FunctionalPathVariable> address, final FunctionalPathVariable subject, final FunctionallableRole role,
			List<ArithmeticExpression> astArgs, Collection<IASTStatement> loops) 
					throws NoSuchVersionException {
//		super(ov, astArgs == null || astArgs.isEmpty() ? 
//				Arrays.asList(computeIndexOf(loops.first(), lv, lv.getCondGen())) : astArgs, null, role);
//		super(ov, null, asn, initRole(astArgs));
//		super(astArgs, null, address, subject, ThreadRole.FUNCTION);	// function role is shared among threads
		super(astArgs, null, address, subject, role);

		assert address != null;
//		if (isZ3ArrayAccess() || toZ3SmtType().startsWith("(Array")) 
//			throwTodoException("Z3 array should be in ArrayAccessVersion");
		
//		this.astArgs = astArgs;
//		if (astArgs != null) for (ArithmeticExpression arg : astArgs) 
//			for (PathVariablePlaceholder argPvp : arg.getDirectPathVariablePlaceholders())
//				for (IASTStatement l : loops) 
//					if (l instanceof IASTForStatement && argPvp.isIteratorOf((IASTForStatement) l)) 
//						throwTodoException("duplicate loop arguments");

		final VODCondGen cg = getSubject().getCondGen();
		final ASTRuntimeLocationComputer rl = new ASTRuntimeLocationComputer(cg);
		init(new TreeMap<>(rl), ()-> debugRun(null, ()-> {
			final SortedSet<IASTStatement> loopSet = new TreeSet<>(rl);
			if (loops != null) loopSet.addAll(loops);
			
			final List<IASTStatement> adloops = address.getDependentLoops();
			if (adloops != null) loopSet.addAll(adloops);
			if (loopSet.isEmpty() && !address.isLoopIterator()) throwTodoException("truly functional");
			
			setArguments(astArgs, loopSet);}, astArgs));
//		argSetter = ()-> setArguments(astArgs, loops);
	}
	
	/**
	 * Copy constructor for privatizing function (arguments).
	 * 
	 * @param address
	 * @param fv
	 * @param role
	 * @throws NoSuchVersionException
	 */
	private FunctionalVersion(final VersionEnumerable<FunctionalPathVariable> address,  
			FunctionalVersion fv, FunctionallableRole role) 
					throws NoSuchVersionException {
		super(null, address, role);
		
		assert fv != null && role != null && !fv.getThreadRole().equals(role);
		init(fv.LoopArgs, fv.argSetter);
	}
	
//	protected FunctionalVersion(LValue lv, 
//			FunctionalPathVariable ov, 
//			Map<LValue, FunctionalVersion> closs, 
//			Map<LValue, FunctionalVersion> posts, 
//			IASTForStatement loop) 
//					throws CoreException, InterruptedException {
//		this(InductiveType.Pre, ov, loop);
//		initials.put(lv, this); 
//		closures = closs;
//		this.posts = posts;
//	}
	
//	protected FunctionalVersion(LValue lv, 
//			Map<LValue, FunctionalVersion> inits, 
//			FunctionalPathVariable ov, 
//			Map<LValue, FunctionalVersion> posts, 
//			IASTForStatement loop) 
//					throws CoreException, InterruptedException {
//		this(InductiveType.Closure, ov, loop);
//		initials = inits;
//		closures.put(lv, this); 
//		this.posts = posts;
//	}
	
//	protected FunctionalVersion(LValue lv, 
//			Map<LValue, FunctionalVersion> inits, 
//			Map<LValue, FunctionalVersion> closs, 
//			FunctionalPathVariable ov, IASTForStatement loop) 
//					throws CoreException, InterruptedException {
//		this(InductiveType.Post, ov, loop);
//		initials = inits;
//		closures = closs;
//		posts.put(lv, this);
//	}

	
	
	private void init(SortedMap<IASTStatement, Pair<ArithmeticExpression, ArithmeticExpression>> largs, Runnable as) {
		LoopArgs = largs;
		argSetter = as;
		
//		setRole(getThreadRole().getBasic().extend(getArguments()));
	}
	
//	static private ThreadRoleMatchable initRole(
//			List<ArithmeticExpression> astArgs) {
//		final ThreadRoleMatchable F = ThreadRole.FUNCTION;
//		if (astArgs != null) 
//			for (ArithmeticExpression arg : astArgs)
//				for (Version<?> ver : arg.getDirectVariableReferences()) {
//					final ThreadRole ar = ver.getRole();
//					if (F.derives(ar)) return ar.extend(astArgs);
//					else throwTodoException("unmatchable role");
//				}
//		return F;
//	}
	

	
	static private Version<? extends PathVariable> from(final FunctionalAssignable asn, 
			List<ArithmeticExpression> astArgs, Collection<IASTStatement> loops) 
					throws NoSuchVersionException {
		assert asn != null && loops != null && !loops.isEmpty();
		final Version<? extends PathVariable> fv = from(asn, astArgs, loops, asn.getCondGen());
		if (fv instanceof FunctionalVersion) asn.setFunctionalVersion((FunctionalVersion) fv);
		else throwNullArgumentException("functional version");
		return fv;
	}
	
	/**
	 * @param address
	 * @param astArgs - arguments other than the {@code loop} iteration one
	 * @param loops
	 * @return
	 * @throws NoSuchVersionException 
	 */
	static public Version<? extends PathVariable> from(final VersionEnumerable<FunctionalPathVariable> address, 
			List<ArithmeticExpression> astArgs, Collection<IASTStatement> loops, VODCondGen condGen) 
					throws NoSuchVersionException {
		if (address == null) throwNullArgumentException("address");

//		if (tests(asn.isDirectlyFunctional())) break asn;
//			
//		final NavigableSet<Assignable> pras = asn.previousRuntimeAssigneds();
//		if (pras.size() != 1) throwTodoException("unsupported function");
//			
//		final Assignable pAsn = (Assignable) pras.first().previousRuntimeAssigneds();
//		// the previous may be constant
//		return from(pAsn, FunctionalPathVariable.from(pAsn), astArgs, loops);

		return from(address, ThreadRole.FUNCTION, 
				()-> new FunctionalVersion(address, address.getVersionSubject(), ThreadRole.FUNCTION, astArgs, loops));
//		if (lvia == null) throwTodoException("unsupported functional version");
//		return tests(address.isAssigned())
//				? (FunctionalVersion) fromSuperversion(address, ThreadRole.FUNCTION, ()-> new FunctionalVersion(address, apv, astArgs, loops))
//				: (FunctionalVersion) from(address, ThreadRole.FUNCTION, ()-> new FunctionalVersion(address, apv, astArgs, loops));
	}
	
	static public Version<? extends PathVariable> from(Assignable<? extends PathVariable> asn) 
			throws NoSuchVersionException {
		return from(asn, ThreadRole.FUNCTION, (Collection<IASTStatement>) null);
	}
	
	/**
	 * @param asn
	 * @param role - the master role of functional version is for self assignments in non-parallel loop
	 * @param loops - can be duplicate if it's parallel.
	 * 	For example, the following code,
	 * 	<code>
	 * 		#pragma omp parallel for  
	 * 		for (int i=0;i< len -1 ;i++)    
	 * 			a[i]=a[i+1]+1;
	 * 	</code>
	 * 	yields two functional versions a[i, i] and a[i+1, i], where the first arguments  
	 * 	<code>i</code> and <code>i+1</code> remain the same while the second (or derived) 
	 * 	arguments <code>i</code>'s means the parallel accessing index.
	 * 
	 * @throws NoSuchVersionException 
	 */
	static public Version<? extends PathVariable> from(
			Assignable<? extends PathVariable> asn, final FunctionallableRole role, Collection<IASTStatement> loops) 
			throws NoSuchVersionException {
//		if (apv == null) throwNoSuchVersionException(asn, "non-array-like assignable");
		if (role == null) throwNullArgumentException("role");
		if (role.equals(ThreadRole.CONST)) throwNoSuchVersionException(asn, "unnecessary functional constant");
		
		final Assignable<?> asn_ = checkPre(asn);
		if (role.equals(ThreadRole.MASTER)) {
			/*
			 * e.g. tmp in the non-parallel loop:
			 * 
			 * #pragma omp parallel for
			 * for (i=0;i<len;i++)
			 * {
			 * 	tmp =a[i]+i;
			 * 	a[i] = tmp;
			 * }
			 */
			assert asn.isThreadPrivate();
			if (!asn.selfAssigns() || !tests(asn.isAssigned())) throwNoSuchVersionException(asn, "non-self assignment");
//			if (!asn.isDeclaredPrivate()) throwNoSuchVersionException(asn, "shared variable with non-functional role");
		} 
		
		// for parallel or dependent loop
		final ArrayPointer array = (ArrayPointer) ArrayPointer.from(asn_);
		final FunctionalAssignable fasn = getNonNull(()-> asn_.toFunctional());
		final boolean rif = role.equals(ThreadRole.FUNCTION);
		if (array == null) return 
//				if (!rif) throwNoSuchVersionException(fasn, "unsupported role")
				from(fasn, (List<ArithmeticExpression>) null, loops);
//		else if (role.isPrivate() && !fasn.isThreadPrivate()) 
//			throwNoSuchVersionException(asn, "shared array should NOT be private");

		if (loops == null || loops.isEmpty()) loops = asn_.getDependentLoops();
		if (loops.isEmpty()) throwTodoException("unsupported loop-less function");

		// for AST array accessing
		final Collection<IASTStatement> funcLoops = new ArrayList<>();
		final VODCondGen cg = asn_.getCondGen();
		for (IASTStatement loop : loops) 
			if (array.hasIteratingArgumentsFrom(loop) || ASTLoopUtil.isLoopParallel(loop, cg))
				funcLoops.add(loop);
		if (funcLoops.isEmpty()) return throwNoSuchVersionException(asn_, "a pure AST array");
		
		final List<ArithmeticExpression> astArgs = array.matchArgumentsTo(array.getArguments(), role);
		FunctionalVersion fv = (FunctionalVersion) from(fasn, astArgs, funcLoops);
		if (rif) return fv;
		
		final VersionEnumerable<FunctionalPathVariable> address = VariablePlaceholder.fromNonAST(fv).cloneIfChangeRole(role);
		fv = (FunctionalVersion) from(address, role, ()-> new FunctionalVersion(address, fasn.getPathVariable(), role, astArgs, funcLoops));
		fv.setName(fasn.getASTName());	// setting AST reference for non-AST versions
		return fv;
	}
	
//	/**
//	 * For block statement reduction and path variable privatization.
//	 * 
//	 * @param asn
//	 * @param args
//	 * @param loop
//	 * @return
//	 * @throws NoSuchVersionException
//	 */
//	static public Version<? extends PathVariable> from(
//			VersionEnumerable<FunctionalPathVariable> asn, List<ArithmeticExpression> astArgs, IASTForStatement loop) 
//					throws NoSuchVersionException {
////		if (args == null) Debug.throwNullArgumentException("function arguments");
//		
//		return from(asn, astArgs, loop, ()-> asn.getCondGen());
//	}
	
//	static public FunctionalIntInputVersion from(IASTForStatement loop, VOPCondGen condGen) {
//		return from(Assignable.fromCanonicalIteratorOf(loop, condGen), loop);
//	}
	
	static private Assignable<?> checkPre(Assignable<?> asn) throws NoSuchVersionException {
		if (asn == null) throwNullArgumentException("assignable");
//		if (asn.isLoopIteratingIterator()) 
//			throwNoSuchVersionException("function argument itself");

		/* only directly-functional-prone arguments 
		 * (functional assignable's or canonical loop iterators) are used
		 */
		if (testsNot(asn.isFunctional())) throwNoSuchVersionException(asn, "non functional " + asn); 
//		if (testsNot(asn.isDirectlyFunctional())) 
//			throwNoSuchVersionException(asn, "loop-independent variable"); 
		
		// only the self functional assigned are counted
		// either assigned or parallel
//		if (asn.isLoopIterator()) asn = (Assignable<? extends PathVariable>) asn.previousOrUnambiguousAssigned();
		return asn;
//		return throwNoSuchVersionException("non-self functional assigned"); 

		// asn depends on loop -> asn's locally assigned in loop
//		final Assignable pAsd = asn.previousAssigned();
//		return pAsd == null 
//			? throwNoSuchVersionException("locally non-assigned")
//			: from(pAsd);	// the previous may be constant
	}
	


//	@Override
//	protected Object cloneNonConstant() {
//		FunctionalVersion clone = (FunctionalVersion) super.cloneNonConstant();
//		clone.funcCallView = funcCallView;
////		clone.astArgs = astArgs;
//		clone.LoopArgs = new TreeMap<>(LoopArgs);
////		clone.fcvSetter = fcvSetter;
//		clone.argSetter = argSetter;
//		return clone;
//	}
	
	@SuppressWarnings("unchecked")
	public FunctionalVersion cloneAssigner() throws NoSuchVersionException {
		final VODCondGen cg = getCondGen();
		final VersionEnumerable<FunctionalPathVariable> asgner2 = (VersionEnumerable<FunctionalPathVariable>) 
				VariablePlaceholder.fromNonAST(getName() + "_2", isGlobal(), false, null, cg, 
						addr-> (FunctionalVersion) from(
						(VersionEnumerable<FunctionalPathVariable>) addr, 
						getAstArguments(), 
						getAssignable().getDependentLoops(), 
						cg));
		return (FunctionalVersion) asgner2.getVersion();
	}
	
	
	
	@SuppressWarnings("unchecked")
	private <T extends ConditionElement> T cloneChangeRole(FunctionallableRole newRole) {
		assert newRole != null && !newRole.equals(getThreadRole());
		try {
//			if (newRole.equals(ThreadRole.FUNCTION)) return (T) this;
//			if (newRole.isPrivate()) return cloneReversion(null, newRole, this);
			final List<ArithmeticExpression> args = getArguments();
			final FunctionallableRole argRole = ThreadRoleMatchable.getThreadRole((Collection<? extends Expression>) args);
			if (argRole.equalsBasic(newRole)) return (T) this;
			
			final Assignable<?> asn = getAssignable();
			if (asn != null && (asn.isLoopIterator() || asn.isDirectiveLocal())) {
				// same address with a new role
				if (newRole.isPrivate()) return asn.debugGet(()-> (T) ThreadPrivateVersion.fromThreadRole(asn, null, null, newRole));
//				if (newRole.isFunctional()) return (T) ThreadPrivateVersion.fromFunctional(asn, null, nr);
			}
			
			// non-AST address with new role arguments
			final ExtendedRole nr = newRole.getBasic().extend(args);
			final VersionEnumerable<FunctionalPathVariable> addr = VariablePlaceholder.fromNonAST(this).cloneIfChangeRole(newRole);
			return (T) asn.debugGet(()-> from(addr, nr, ()-> new FunctionalVersion(addr, this, nr)));
			
		} catch (NoSuchVersionException e) {	// invalid version under AST
			return throwTodoException(e);
		}
//		return super.cloneIfChangeRole(newRole);
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public <T extends ConditionElement> T cloneIfChangeRole(FunctionallableRole newRole) {
		try {
//			final T sc = super.cloneIfChangeRole(newRole);
			final T sc = cloneReversion(null, newRole, this);
			return sc == this
					? (T) this
					: cloneChangeRole(newRole);
			
		} catch (NoSuchVersionException e) {	
			return cloneChangeRole(newRole);

		} catch (Exception e) {	
			return throwTodoException(e);
		}
//		return super.cloneIfChangeRole(newRole);
	}

	/**
	 * @param role - private roles indicate private arguments but NOT a {@link ThreadPrivateVersion}.
	 * @return pure clone in {@link FunctionalVersion} type.
	 */
	@SuppressWarnings("unchecked")
	@Override
	public <T extends ConditionElement> T cloneReversion(
			final IASTStatement blockStat, FunctionallableRole role, Version<? extends PathVariable> ver) {
//		if (equalsFunctionBasic(role)) return (T) this;

		try {
			return (T) super.cloneReversion(blockStat, role, (Version<? extends PathVariable>) this);
//			return asn.debugGet(()-> (T) super.cloneReversion(blockStat, role, (Version<? extends PathVariable>) this));
			
		} catch (NoSuchVersionException e) {
			final Assignable<?> asn = getAssignable();
			return (T) asn.debugGet(()-> from(asn, role, getLoops()));

		} catch (Exception e) {
			return throwTodoException(e);
		}
		
//		if (role != null) try {
//			if (role.equals(ThreadRole.FUNCTION)) return (T) this;
//			if (role.isPrivate()) {
//				final FunctionalAssignable fasn = getFunctionalAssignable();
//				if (role instanceof ExtendedRole) 
//					return (T) ThreadPrivateVersion.fromFunctional(fasn, blockStat, (ExtendedRole) role);
//				else {
//					final ThreadRole tr = (ThreadRole) role;
//					return (T) ThreadPrivateVersion.fromFunctional(fasn, blockStat, isLoopIterator() ? tr.extend(fasn) : tr.extend(getArguments()));
//				}
//			}  
//			
//		} catch (NoSuchVersionException e) {
//			throw e;
//		} catch (Exception e) {
//			return throwTodoException(e);
//		}
//		return super.cloneReversion(blockStat, role, ver);
	}
	
	
	
	@Override
	protected Boolean cacheConstant() {
		return false;
	}
	
//	/**
//	 * @return non-null subject's side-effects.
//	 */
//	protected VOPConditions cacheDirectSideEffect() {
//		VOPConditions se = new VOPConditions(getCondGen());
//		Set<FunctionalVersion> q = Collections.singleton(this);
//		// initials
//		se.and(Forall.from(q, ));
//		// closures
//		se.and(Forall.from(q, ));
//		// posts
//		se.and(Forall.from(q, ));
//		return se;
//	}

	

//	public FunctionalVersion getInitialVersion(LValue ov)	{return initials.get(ov);}
//	public FunctionalVersion getClosureVersion(LValue ov)	{return closures.get(ov);}
//	public FunctionalVersion getPostVersion(LValue ov) 		{return posts.get(ov);}
	
	
	
	@Override
	protected void checkArguments() {
//		if (argSetter != null) getAssignable().debugCallDepth(()-> getAssignable().guard(()-> {
		if (argSetter != null) {
			argSetter.run(); 
			argSetter = null;
			super.checkArguments();
		}
	}

//	@Override
//	protected boolean checksArguments(ArithmeticExpression arg1, ArithmeticExpression arg2) {
//		return arg1 == null || arg2 == null || super.checksArguments(arg1, arg2);
//	}
	
	@SuppressWarnings("unchecked")
	private List<ExpressionRange<? extends Expression>> getArgumentRanges(IASTStatement loop) {
		if (!argRanges.isEmpty()) return argRanges;
		
		final ArithmeticExpression[] bs = ASTLoopUtil.getBoundsOf(loop);
		final ArithmeticExpression lb = bs[0], ub = bs[1];
		final PathVariablePlaceholder li = getLoopArgument(loop);
		for (ArithmeticExpression aa : getArguments()) {
			final Expression aae = aa.toExpression();
			if (!tests(aae.dependsOn(li))) continue;
			argRanges.add((ExpressionRange<? extends Expression>) ExpressionRange.from(aae, lb, ub));
		}
		return argRanges;
	}
	
	@Override
	public List<ArithmeticExpression> getArguments() {
		checkArguments();
		final List<ArithmeticExpression> args = 
				new ArrayList<>(super.getArguments());
		for (Pair<ArithmeticExpression, ArithmeticExpression> la : getLoopArguments()) {
			final ArithmeticExpression la1 = la.getPeer1(), la2 = la.getPeer2();
			args.add(la1);
			if (hasLoopEnumer()) {	
//			if (!isArgument() && la1.isPrivate()) {	// isArgument => hasNoEnumer
				if (la2 == null) throwNullArgumentException("enumer");
				args.add(la2);
			} else if (la2 != null) throwTodoException("ignored loop enumer");
		}
//		if (LoopArgs != null || !LoopArgs.isEmpty())
//			for (Entry<IASTStatement, Pair<ArithmeticExpression, ArithmeticExpression>> la : LoopArgs.entrySet()) 
//				for (ArithmeticExpression arg : new ArrayList<>(args))
//					if (!arg.dependsOnAnyDirectly(getLoopIterators())) args.add(la.getPeer1());
		return args;
	}
	
	/**
	 * @return non-null
	 */
	@Override
	public List<ArithmeticExpression> getAstArguments() {
		checkArguments();
		return super.getArguments();
//		return astArgs == null
//				? Collections.emptyList()
//				: astArgs;
	}
	
	public PathVariablePlaceholder getLoopArgument(IASTStatement loop) {
//	public ArithmeticExpression getLoopArgument(IASTStatement loop) {
		if (loop == null) throwNullArgumentException("loop");
//		checkArguments();
//		return LoopArgs.get(loop);
		try {
		return PathVariablePlaceholder.fromCanonicalIteratorOf(
						(IASTForStatement) loop, cacheRuntimeAddress(), getCondGen());
		
		} catch (ASTException | ClassCastException | IncomparableException | UncertainPlaceholderException | NoSuchVersionException e) {
			return throwTodoException("unsupported loop", e);
		}
	}
	
	/**
	 * @return non-null
	 */
	public Collection<Pair<ArithmeticExpression, ArithmeticExpression>> getLoopArguments() {
		checkArguments();
		return LoopArgs == null
				? Collections.emptyList()
				: LoopArgs.values();
	}
	
	
	
//	@Override
//	public boolean addArgument(ArithmeticExpression arg) {
//		return throwTodoException("getLoop(arg)");
////		if (arg == null) return false;
////		return super.addArgument(arg.reversion(getLoop(arg), getRole(), null));
//	}

	/**
	 * For the self functional version index as loop iterator.
	 * @param loop
	 * @return
	 */
	private boolean setArgument(IASTStatement loop) {
		assert loop != null;
		return LoopArgs.put(loop, new Pair<>(this, getLoopEnumer(this, loop))) 
				!= null;
	}
	
	private boolean setArgument(
			IASTStatement loop, ArithmeticExpression astIndex) {
		assert loop != null && astIndex != null && astIndex != this;
		try {
			return LoopArgs.put(loop, new Pair<>(astIndex, getLoopEnumer(astIndex, loop))) 
					!= null;
//			checkArgumentRole(index);
			
//		} catch (NoSuchVersionException e) {
		} catch (Exception e) {
			return throwTodoException(e);
		}
	}

	/**<pre>
	 * loop_1[in_1, ub_1]
	 * 	...
	 * loop_x[in_x, ub_x]
	 * lv(astArgs..., index_1, index_2, ..., in_x, ..., index_n)
	 * 	...
	 * loop_n[in_n, ub_n]								
	 * </pre>
	 * 
	 * @param loop
	 */
	private void setArgument(final ArithmeticExpression astArg, final IASTStatement loop) {
		assert loop != null;
		if (isIteratorOf(loop))
			setArgument(loop);
		else 
			setArgument(loop, astArg != null ? astArg : computeIndexOf(loop));
	}
	
	/**
	 * @param astArgs
	 * @param loops
	 */
	private void setArguments(
			List<ArithmeticExpression> astArgs, SortedSet<IASTStatement> loops) {
//		if (astArgs != null) setArguments(astArgs);
		
		for (IASTStatement loop : loops) {
			if (astArgs == null || astArgs.isEmpty()) 
				setArgument(null, loop);
			else for (ArithmeticExpression arg : astArgs) 
				setArgument(arg, loop);
		}
	}
	
	@Override
	public void setAddress(VersionEnumerable<FunctionalPathVariable> addr) {
		if (addr instanceof FunctionalAssignable) 
			((FunctionalAssignable) addr).setFunctionalVersion(this);
		super.setAddress(addr);
	}
	
	@Override
	protected void setRole(FunctionallableRole role) {
		super.setRole(role);
		
		assert role != null;
		if (!role.isFunctional()) 
//		if (!role.equals(ThreadRole.FUNCTION)) 
			throwInvalidityException("inconsistent role");
	}
	
//	@Override
//	public FunctionalPathVariable setSubject(FunctionalPathVariable newSubject) {
//		assert newSubject instanceof FunctionalPathVariable;
//		return super.setSubject(newSubject);
//	}

	
	
	/**<pre>
	 * Modeling multi-loop index with the decidable stratified sorts fragment of 
	 * many sorted first-order logic formulas.
	 * 
	 * Case independent loops:
	 * 
	 * ... f(lb_i + pre_i_count, lb_j + pre_j_count) = ...
	 * for(i = lb_i; i <= ub_i; i++) {
	 * 		... f(local_i_count*(i-lb_i+1), ..) = ...	
	 * }
	 * ... f(local_ub_i_count*(ub_i-lb_i+1) + post_i_count, ..) = ...
	 * for(j = lb_j; j <= ub_j; j++) {
	 * 		... f(.., local_j_count*(j-lb_j)) = ...
	 * }
	 * ... f(.., local_ub_j_count*(ub_j-lb_j+1) + post_j_count) = ...
	 * 
	 * Case dependent (nested) loops:
	 * 
	 * ... f(lb_i + pre_i_count, lb_j + pre_j_count) = ...
	 * for(i = lb_i; i <= ub_i; i++) {
	 * 		... f(local_i_count*(i-lb_i+1), ..) = ...	
	 * 		for(j = lb_j; j <= ub_j; j++) {
	 * 		... f(.., local_j_count*(j-lb_j+1)) = ...
	 * 		}
	 * 		... f(.., local_ub_j_count*(ub_j-lb_j+1) + post_j_count) = ...
	 * }
	 * ... f(local_ub_i_count*(ub_i-lb_i+1) + post_i_count, ..) = ...
	 * 
	 * TODO: linearize f for higher efficiency?
	 * Ex., Case independent loops:
	 * 
	 * ... f(i < lb_i) ...
	 * for(i = lb_i; i <= ub_i; i++) {... f(i) ...}
	 * ... f(ub_i < n <= ub_i + count_ij) = ...
	 * for(j = lb_j; j <= ub_j; j++) {... f(ub_i + count_ij + 1 + (j - lb_j)) ...}
	 * ... f(n > ub_i + count_ij + 1 + (ub_j - lb_j)) ...
	 * 
	 * TODO: handle general for-loops rather than just canonical ones. 
	 * </pre>
	 * 
	 * @param loop
	 * @return null if lv is independent to {@code loop}
	 */
	static private ArithmeticExpression computeIndexOf(
			IASTForStatement loop, Assignable<FunctionalPathVariable> asn, final VODCondGen condGen) {
		assert loop != null && asn != null; 
//		assert lv.dependsOn(lv.getEnclosingCanonicalLoopIterator());
		
		try {
		// computing indexes (both in- and upper-bound ones) of tLoop
		final ASTAddressable ra = asn.getRuntimeAddress();
		final ArithmeticExpression 
//				count = Int.from(ConstantCountingVersion.countIn(asn, loop), asn.getShortAddress()),
				lb = ArithmeticExpression.fromLowerBoundOf(loop, ra, condGen);
		ArithmeticExpression[] lis = LOOP_INDEXES.get(loop);
		ArithmeticExpression inIndex = null, ubIndex = null;
		if (lis != null) {
			inIndex = lis[0]; ubIndex = lis[1];
		} else {
			final Assignable<?> it = Assignable.fromCanonicalIteratorOf(loop, ra, condGen);
			// TODO: if asn is shared b/w loops
//			inIndex = it.getPathVariablePlaceholder().subtract(lb).add(Int.ONE);
			inIndex = it.getPathVariablePlaceholder();
			if (it == asn) return inIndex;	// iterator as self index

//			ubIndex = count.multiply(ArithmeticExpression.fromUpperBoundOf(loop, ra, condGen).subtract(lb).add(Int.ONE));
			ubIndex = ArithmeticExpression.fromUpperBoundOf(loop, ra, condGen).subtract(lb).add(Int.ONE);
			LOOP_INDEXES.put(loop, new ArithmeticExpression[] {inIndex, ubIndex});
		}
		
		final IASTNode asnTop = asn.getTopNode();
		final ASTRuntimeLocationComputer rlc = new ASTRuntimeLocationComputer(condGen);
		/* 
		 * tLoop					firstLoop = tLoop		firstLoop				firstLoop			firstLoop
		 * lv(lb1-c1,...,lbn-cn)	lv(lb1+c1,...lbn-cn)	lv(lb1+c1,...lbn-cn)	lv					lv
		 * firstLoop[lb1,ub1]		lastLoop				tLoop[lbt,ubt]			lastLoop = tLoop	lastLoop
		 * lv												lastLoop				tLoop
		 * lastLoop[lbn,ubn]								
		 * 
		 */
		// local_i_count*(i-lb_i+1)
		assert !asn.isIteratorOf(loop);
		if (rlc.isIn(asnTop, loop)) {
//			final ArithmeticExpression idx = count.multiply(inIndex);
			final ArithmeticExpression idx = inIndex;
			// for(i=lb;i<=ub;i++) frc1(j, i) = frc1(j-1, i-1) + ...
			return asn.selfAssigns() ? idx.subtract(Int.ONE) : idx;
		
		/* lb_i + pre_i_count:
		 * Representing pre-loop function calls, ex. frc1(j, lb+preCount) for 
		 * for(i=lb;i<=ub;i++) frc1(j, i) = frc1(j-1, i-1) + ...
		 */
//		} else if (rlc.isBefore(asnTop, loop)) return lb.add(count);
		} else if (rlc.isBefore(asnTop, loop)) return lb.add(Int.ONE);
		
		// local_ub_i_count*(ub_i-lb_i+1) + post_i_count
//		else return ubIndex.add(count);
		else return ubIndex.add(Int.ONE);
		
		} catch (Exception e) {
			throwTodoException("unsupported arithmetic expression");
		}
		return null;
	}
	
	@SuppressWarnings("unchecked")
	private ArithmeticExpression computeIndexOf(IASTStatement loop) {
		if (loop instanceof IASTForStatement) {
			final Assignable<?> asn = getAssignable();
			final VODCondGen cg = getCondGen();
			final IASTForStatement forLoop = (IASTForStatement) loop;
			return asn != null
					? computeIndexOf(forLoop, (Assignable<FunctionalPathVariable>) asn, cg)
					: computeIndexOf(forLoop, (Assignable<FunctionalPathVariable>) Assignable.fromCanonicalIteratorOf(forLoop, getRuntimeAddress(), cg), cg);
		}
//		if (loop instanceof IASTWhileStatement)
//			return computeIndexOf((IASTWhileStatement) loop, asn, cg);
		return throwTodoException("unsupported loop");
	}
	
//	private ArithmeticExpression getInIndexOf(IASTForStatement tLoop) {
//	private ArithmeticExpression getInIndexOf(IASTForStatement tLoop) {

	
	
//	@Override
//	public Expression getAssignerIf() {
//		return isArgument()
//				? super.getAssignerIf()
//				: getFuncCallView();
//	}

//	@Override
//	public void setAssigner(Expression rhs) {
//		super.setAssigner(rhs);
//		generateRaceAssertion();
//	}
	
	/**
	 * @return true if it's self-assigned.
	 */
	public boolean selfAssigns() {
		return tests(()-> getAssignable().selfAssigns());
//		return !getSelfAssigners().isEmpty();
	}
	
	/**
	 * @return non-null
	 */
	public List<FunctionalVersion> getSelfAssigners() {
		final List<FunctionalVersion> sas = new ArrayList<>();
		
		if (tests(isAssigned())) {
			@SuppressWarnings("unchecked")
			final FunctionalPathVariable fpv = FunctionalPathVariable.from((Assignable<FunctionalPathVariable>) getAssignable());
			for (Version<?> asgnr : 
				getNonNull(()-> getAssigner().getDirectVariableReferences())) try {
					if (asgnr.equalsSubject(fpv)) sas.add((FunctionalVersion) asgnr);

				} catch (Exception e) {
					throwTodoException(e);
				}
		}
		return sas;
	}

	@Override
	public NavigableSet<? extends Assignable<?>> getAssigneds() {
		try {
			return hasAssignable()
					? super.getAssigneds()
					: getAdjacentAssignable().getAssigneds();
			
		} catch (Exception e) {
			return throwTodoException(e);
		}
	}

	public Assignable<?> getAdjacentAssignable() {
		return get(()-> getAssignable(),
				()-> Assignable.from(getASTName(), getRuntimeAddress(), getCondGen()));
	}
	

	
//	@Override
//	public PlatformType getType() {
//		return isInAST() || isArgument()
//				? getAssignable().getType()
//				: super.getType();
//	}

	/**
	 * @param loop
	 * @return Loop-dependent type - 
	 * {@link InductiveType#Closure} if enclosed by {@code loop}.
	 */
	public InductiveType getType(IASTForStatement loop) {
		if (loop == null) throwNullArgumentException("loop");
		
		for (IASTStatement l : LOOP_INDEXES.keySet()) 
			if (l.equals(loop)) return InductiveType.Closure;
		
		if (new ASTRuntimeLocationComputer(getCondGen())
				.isBefore(getAssignable().getTopNode(), loop)) 
			return InductiveType.Pre;
		return InductiveType.Post; 
	}
	
	@Override
	public PlatformType getCodomainType() {
		final PlatformType at = getAddress().getType();
		return at instanceof PointerType
				? ((PointerType) at).getPointToEndType()
				: at;
	}
	
//	public OmpDirective getEnclosingDirective() {
//		return 
//	}
	
	public Function getFunction() {
		return isArgument()
				? null
				: Function.from(this);
//		return getSkipNull(()->
//		getFuncCallView().getSubject());
	}
	
	public FunctionalAssignable getFunctionalAssignable() {
		try {
		return (FunctionalAssignable) getAssignable();
		
		} catch (ClassCastException e) {
			return throwTodoException(e);
		}
	}

	public FunctionCall<?> getFuncCallView() {
		if (funcCallView != null || isLoopIterator()) return funcCallView;
		
		// FunctionCall.from depends on getArguments()
		funcCallView = FunctionCall.from(this, ()-> toProposition());
		if (funcCallView == null) throwNullArgumentException("function");
		return funcCallView;
	}
	
	
	
	/**
	 * @return non-null
	 */
	public Set<IASTStatement> getLoops() {
		return get(()-> getNonNull(()-> LoopArgs).keySet(),
				()-> Collections.emptySet());
	}
	
	private ArithmeticExpression getLoopEnumer(ArithmeticExpression astIndex, final IASTStatement loop) {
		assert loop != null;
		if (!hasLoopEnumer()) return null;
		
		if (loop instanceof IASTForStatement) try {
			final ConditionElement scope = getScope();
			final ASTAddressable rtAddr = cacheRuntimeAddress();
			final VODCondGen cg = getCondGen();
			final List<Assignable<?>> its = getLoopIterators();
			final List<PathVariablePlaceholder> itps = Assignable.toPlaceholders(its);
			final String name = Assignable.fromCanonicalIteratorOf((IASTForStatement) loop, rtAddr, cg).getShortNameAddress() + "_enumer";
			final Function f = Function.from(ASTUtil.toLocationOf(loop), name, DataType.Int, cg, Parameter.from(itps));
			final FunctionCall<?> enumer = FunctionCall.from(f, name, itps, scope);
			final ArithmeticExpression enumerNext = enumer.add(Int.ONE);
			if (astIndex.contains(its)) {
				/*
				 * a[i][j] += a[i + 1][j] 
				 * => a(i, j, loop_enumer(i,j) + 1) = a(i, j, loop_enumer(i,j)) + a(i + 1, j, loop_enumer(i,j)) 
				 * 	&& forall (i,j,i2,j2) (i2 = i && j2 = j) -> loop_enumer(i2,j2) > loop_enumer(i,j) + 1
				 */
				Proposition prop = null;
				final Set<VariablePlaceholder<?>> qs = new HashSet<>(itps);
				final List<VariablePlaceholder<?>> itp2s = new ArrayList<>();
				for (PathVariablePlaceholder itp : itps) {
					final VariablePlaceholder<?> itp2 = VariablePlaceholder.fromSelfAssigning(itp);
					final Proposition itpeq = itp.equal(itp2);
					itp2s.add(itp2);
					qs.add(itp2);
					prop = prop == null ? itpeq : prop.and(()-> itpeq);
				}
				final Proposition prop_ = prop;
				andSideEffect(()-> Forall.from(qs, prop_.imply(()-> enumerNext.lessThan(FunctionCall.from(f, name, itp2s, scope))))); 

			} else {
				/*
				 * xa1[idx]+= 1.0 + i => xa1[indexSet[i]]+= 1.0 + i 
				 * => xa1(indexSet[i], loop_enumer(i) + 1) = xa1(indexSet[i], loop_enumer(i)) + 1.0 + i
				 *   	&& forall (i,i2) (i2 > i && indexSet[i2] = indexSet[i] -> loop_enumer(i2) > loop_enumer(i) + 1),
				 */
				final PathVariablePlaceholder itp = Assignable.fromCanonicalIteratorOf((IASTForStatement) loop, rtAddr, cg).getPathVariablePlaceholder();
				final VariablePlaceholder<?> itp2 = VariablePlaceholder.fromSelfAssigning(itp);
				andSideEffect(()-> Forall.from(new HashSet<>(Arrays.asList(itp, itp2)), 
						itp.lessThan(itp2).and(astIndex.cloneReindex(itp, itp2).equal(astIndex)).imply(()-> 
						enumerNext.lessThan(FunctionCall.from(f, name, Arrays.asList(itp2), scope)))));
			}
			return tests(isAssigned()) ? enumerNext : enumer;
			
		} catch (NoSuchVersionException e) {
			throwTodoException(e);
		}
		return throwTodoException("unsupported loop");
	}
	
	private List<Assignable<?>> getLoopIterators() {
		final Assignable<?> asn = getAssignable();
		final ASTAddressable da = cacheRuntimeAddress();
		final List<Assignable<?>> its = new ArrayList<>();
		for (IASTStatement b : asn.getBranchScopes())
			if (b instanceof IASTForStatement) 
				its.add(0, Assignable.fromCanonicalIteratorOf((IASTForStatement) b, da, getCondGen()));
		return its;
	}
	
	/**
	 * @return a non-null list.
	 */
	@SuppressWarnings("unchecked")
	public List<ExpressionRange<Version<Variable>>> getLoopRanges() {
		final ASTAddressable da = cacheRuntimeAddress();
		final VODCondGen condGen = getCondGen();
		final ASTRuntimeLocationComputer rlc = new ASTRuntimeLocationComputer(condGen);
		final IASTNode lvn = getAssignable().getTopNode();
		final List<ExpressionRange<Version<Variable>>> drs = new ArrayList<>();
		Proposition vr = null;
		for (IASTStatement l : LOOP_INDEXES.keySet()) {
			if (rlc.isIn(lvn, l)) 
				vr = ExpressionRange.fromIteratorOf(l, da, condGen);
//			else if (lv.isIteratorOf(l)) 
//				continue; 
//			else if (rlc.isBefore(lvn, l)) 
//				vr = ExpressionRange.fromIteratorBefore(l, condGen);
			else 
				vr = ExpressionRange.fromIteratorAfter(l, da, condGen);
			
			if (vr instanceof ExpressionRange) 
				drs.add((ExpressionRange<Version<Variable>>) vr);
			else throwTodoException("unsupported variable range");
		}
		
		assert drs.size() == getArguments().size();
		return drs;
	}
	
	/**
	 * @param loop
	 * @return
	 */
	public IASTForStatement getPreLoop(IASTForStatement loop) {
		throwTodoException("Get the first l-value within loop first!");
		return null;
	}
	
	@SuppressWarnings("unchecked")
	public IASTForStatement getPreLoop(Assignable<?> lv) {
		if (lv == null || !FunctionalPathVariable.from((Assignable<FunctionalPathVariable>) lv).equals(getSubject())) 
			return null;
		return getPreLoop(lv, ASTUtil.getEnclosingForOf(lv.getTopNode()), getCondGen());
	}
	
	/**
	 * @param loop
	 * @param condGen 
	 * @return
	 */
	@SuppressWarnings("unchecked")
	private IASTForStatement getPreLoop(
			Assignable<?> lv, IASTForStatement loop, VODCondGen condGen) {
		assert lv != null && loop != null 
				&& FunctionalPathVariable.from((Assignable<FunctionalPathVariable>) lv).equals(getSubject()); 
		
		IASTForStatement lvLoop = ASTUtil.getEnclosingForOf(lv.getTopNode());
		if (lvLoop == null || lvLoop == loop) {
			SortedSet<Assignable<?>> preLvs = 
					condGen.getWritingHistoryOfBeforeTP(lv).headSet(lv);
			if (preLvs.isEmpty()) return null;
			return getPreLoop(preLvs.last(), loop, condGen);
		}
		return lvLoop;
	}
	
	

	/**
	 * 1) Updating parent versions for both functional and non-functional subversion's
	 * 2) Adding side-effect with inter-version equivalence: f(args) = f(old_args)
	 * 
	 * @see ompca.condition.version.UbiquitousVersion#checkUbiquitous()
	 */
	@SuppressWarnings("unchecked")
	public void checkUbiquitous() {
		final FunctionalAssignable asn = (FunctionalAssignable) getAssignable();
		if (asn == null) return;
		final Assignable<FunctionalPathVariable> plv = asn.previous();
		if (plv == null) return;
		final List<IASTStatement> ploops = plv.getDependentLoops();
//		if (ploops.isEmpty()) throwTodoException("loop-less functional");
		
		// 1)
		try {
		if (!tests(plv.isConstant())) consumeNonNull(
				fv -> ((FunctionalVersion) fv).checkUbiquitous(),
				()-> from((FunctionalAssignable) plv, getAstArguments(), ploops));

		// 2)
		final VariablePlaceholder<PathVariable> vd = PathVariablePlaceholder.from(asn);
		vd.andSideEffectThrow(()-> Equality.from(vd, PathVariablePlaceholder.from(plv)));
		} catch (Exception e) {
			throwTodoException(e);
		}
	}

	
	
	/* (non-Javadoc)
	 * @see ompca.condition.version.UbiquitousVersion#enumerate(ompca.condition.Referenceable)
	 */
	@Override
	public <E extends VersionEnumerable<? super FunctionalPathVariable>> 
	EnumeratedVersion<FunctionalPathVariable, E> 
	enumerate(E enumer) throws UnsupportedOperationException {
		
		return throwTodoException("unsupported enumeration");
//		try {
//			EnumeratedVersion<FunctionalPathVariable, E> ev = (EnumeratedVersion<FunctionalPathVariable, E>) 
//			EnumeratedVersion.from(getFunctionAssignable(), getThreadRole());
//			ev.subversion(this);
//			
//			// updating ID's according to the serialization-based subversion-ing rule
//			final String id = ev.getID(SerialFormat.Z3_SMT);
//			setName(id);	
//			getFuncCallView().setName(id);
//			return ev;
//
//		} catch (Exception e) {
//		}
	}
	
	
	
	public boolean equalsFunction(FunctionalVersion fv2) {
		return fv2 != null && getFunction() == fv2.getFunction();
	}

	public boolean equalsFunctionBasic(FunctionallableRole role) {
		return role != null && role.equals(ThreadRole.FUNCTION)
				&& getThreadRole().equals(ThreadRole.FUNCTION);
	}
	
	@Override
	protected boolean equalsToCache(SystemElement e2) {
		if (!super.equalsToCache(e2)) return false;
		
		final FunctionalVersion fv2 = (FunctionalVersion) e2;
		if (getAddress() != fv2.getAddress()) return false;
//		if (astArgs == null) {
//			if (astArgs != fv2.astArgs) return false; 
//		} else if (!astArgs.equals(fv2.astArgs)) return false;	// including fv2.astArgs == null 
		
		assert LoopArgs != null && fv2.LoopArgs != null;
		return guard(()-> !LoopArgs.equals(fv2.LoopArgs),
				// super.equalsToCache(e2) && reentering -> equalsToCache(e2)
				()-> true);	
//				&& funcCallView == fv.funcCallView && lastFuncCallView == fv.lastFuncCallView;
//				&& initials.equals(fv.initials) && closures.equals(fv.closures) && posts.equals(fv.posts);
	}
	
	@Override
	protected List<Integer> hashCodeVars() {
		assert LoopArgs != null;
		final List<Integer> vars = new ArrayList<>(super.hashCodeVars());
//		vars.add(getAddress().hashCode());
//		vars.add(astArgs == null ? 0 : astArgs.hashCode());
		guard(()-> vars.add(LoopArgs.hashCode()), ()-> false);
		return vars;
	}

	
	
	/**
	 * @return false if the assignable is a self-assigning/assigned iterator.
	 */
	public boolean hasLoopEnumer() {
		return !isLoopIterator()
				&& (isSelfAssigned() || selfAssigns());
	}
	
//	/**
//	 * Serialized at the top level for Z3-SMT formats.
//	 * @param sub
//	 * @param format
//	 * @return
//	 */
//	@Override
//	public boolean superversions(Version<? extends FunctionalPathVariable> sub, SerialFormat format) {
//		return true;
//	}
	
	
	
	@Override
	public boolean dependsOn(Variable v) {
		if (super.dependsOn(v)) return true;
		if (!isArgument() && getFuncCallView().dependsOn(v)) return true;
		for (Pair<ArithmeticExpression, ArithmeticExpression> arg : getLoopArguments()) 
			if (arg.getPeer1().toExpression().dependsOn(v)) return true;
		return false;
	}
	
	/**
	 * @return true if this is functional argument too; false if not in AST
	 */
	@Override
	public boolean isArgument() {
		return isLoopIterator() 
				|| (hasAssignable() && super.isArgument());
//		TODO: || getArguments().contains(this);
	}

	@Override
	public boolean isFunctional() {
		return true;
	}
	
	public boolean isIteratorOf(final IASTStatement loop) {
		if (loop instanceof IASTForStatement) try {
			final IASTForStatement forLoop = (IASTForStatement) loop;
			return get(()-> getAssignable().isIteratorOf(forLoop),
					()-> getSubject().isIteratorOf(forLoop));
			
		} catch (ClassCastException e) {
			throwTodoException(e);
		}
		return throwTodoException("unsupported loop");
	}
	
	public boolean isLoopIterator() {
		return get(()-> getAssignable().isLoopIterator(),
				()-> getSubject().isLoopIterator());
	}
	
	public boolean isSelfAssigned() {
		return tests(()-> getAssignable().isSelfAssigned());
	}
	
	@Override
	public boolean isZ3ArrayAccess() {
		return false;
	}
	
	
	
	@Override
	public boolean matches(ThreadRoleMatchable matchable2) {
		if (matchable2 instanceof ExtendedRole) {
			final ThreadRoleMatchable role = peekRole();
			// role == null => version is NOT initialized yet
			if (role != null) {
				final ExtendedRole er2 = (ExtendedRole) matchable2;
				final List<ArithmeticExpression> args = getNonNull(()-> (ExtendedRole) role).getArguments(),
						args2 = er2.getArguments();
				return tests(()-> args == args2 || args.equals(args2));	// args2 != null => er2.isFunctional()
			}
			
//		} else if (matchable2 instanceof FunctionalVersion) {
//			if (getAssignable().isLoopInitializedIterator())
//				return ((FunctionalVersion) matchable2).getAssignable().isLoopIterator();
		}
		// ..._FUNCTION(..._FUNCTION/THREADx, ..._FUNCTION/THREADx, ...)
		return super.matches(matchable2);
	}
	
	@Override
	public ArgumentMatchable matchTo(final ThreadRoleMatchable newRole) {
		return newRole instanceof FunctionallableRole
				? cloneIfChangeRole((FunctionallableRole) newRole)
				: throwUnsupportedRoleException();
	}
	

	
	public Proposition generateRaceAssertion() {
		final List<FunctionalVersion> sas = getSelfAssigners();
		if (sas.isEmpty()) return null;
		
		final List<ArithmeticExpression> args = getArguments();
		final int aasize = args.size();
		if (aasize == 0) return null;	// for functional arguments
		
		boolean hasDirs = false;
		final ASTAddressable da = cacheRuntimeAddress();
		final VODCondGen cg = getCondGen();
		for (FunctionalVersion sa : sas) {
			for (IASTStatement l : getLoops()) try {
				final OmpDirective dir = OmpDirective.fromEnclosing(l, cg);
				if (dir == null) continue;	// l is not in parallel
				else hasDirs = true;
				
				if (!(l instanceof IASTForStatement)) throwTodoException(
						"unsupported loop");
				final PathVariablePlaceholder li = PathVariablePlaceholder
						.fromCanonicalIteratorOf((IASTForStatement) l, da, cg);
				for (int i = 0; i < aasize; i++) {
					final ArithmeticExpression arg = args.get(i);
					final Expression arge = arg.toExpression();
					// assert arg (ast_i) is functional (loop-bounded function index)
					
					// f(ast_i, loop_j) = ... f(ast_i2, loop_j2) ...
					if (tests(arge.dependsOn(li))) {
						final Assignable<?> lia = li.getAssignable();
						setArgument(l, ThreadPrivateVersion.fromThread1(
								lia, l, null));
						sa.setArgument(l, ThreadPrivateVersion.fromThread2(
								lia, l, null));
					}
				}
				
			} catch (NoSuchVersionException e) {
				throwTodoException(e);
			}
		}
		return hasDirs ? 
				generateRaceAssertion(getAssignment().toEquality(), sas) : null;
	}
	
	/**<pre>
	 * Race I: Anti-dependency
	 * For every self-functional assignment f(ast_i, loop_j) = ... f(ast_i2, loop_j) ...
	 * it may cause functional inconsistency in different loop iteration schedules.
	 * 
	 * @param sas
	 * @return the inductive condition of parallel iteration schedule:
	 * 	[Initial/pre-condition]
	 * 	<code>
	 * 	forall lb <= (ast_i) <= ub, loop_j < lb, f(ast_i, loop_j) = fpre(ast_i)
	 * 	</code>
	 * 
	 * 	[Closure condition]
	 * 	<code>
	 * 	forall lb <= (ast_i, ast_i2, loop_j, loop_j2, loop_j3) <= ub, 
	 * 	f(ast_i, loop_j) = ... f(ast_i2, loop_j2) ... && 
	 * 	((/\ ast_i == ast_i2) => loop_j != loop_j2) &&
	 * 		<b>[(/\ ast_i == ast_i2) && loop_j == loop_j2 => false (no race)]</b>
	 * 		[(/\ ast_i == ast_i2) && loop_j != loop_j2 => accessing the same location in different iterations] 
	 * 	(f(ast_i, loop_j) = ... f(ast_i2, loop_j2) ... => 
	 * 		f(ast_i, loop_j) != f(ast_i, loop_j3) && loop_j != loop_j3)
	 * 	</code>
	 * 
	 * 	[Post condition]
	 * 	<code>
	 * 	forall lb <= (ast_i) <= ub, loop_j > ub, f(ast_i, loop_j) = fpost(ast_i)
	 * 	</code>
	 */
	@SuppressWarnings("unchecked")
	private Proposition generateRaceAssertion(Proposition asm, List<FunctionalVersion> sas) {
		assert sas != null && !sas.isEmpty();
		
		Proposition race = null;
		final List<ArithmeticExpression> args = getArguments();
		for (FunctionalVersion sa : sas) {
			for (IASTStatement l : sa.getLoops()) try {
				//	/\ ast_i == ast_i2
				Proposition aaRacePres = null;
				for (int i = 0; i < args.size(); i++) {
					final ArithmeticExpression aa1 = args.get(i).cloneReversion(l, ThreadRole.THREAD1, null), 
							aa2 = sa.getArgument(i).cloneReversion(l, ThreadRole.THREAD2, null);
					final Proposition aaRacePre = aa1.equal(aa2);
					aaRacePres = aaRacePres == null ? 
							aaRacePre : aaRacePres.and(aaRacePre);
				}
				
				// Initial/pre-condition
				//	forall lb <= (ast_i) <= ub, loop_j < lb, f(ast_i, loop_j) = fpre(ast_i)
				
				// Closure condition
				// 	f(ast_i, loop_j) = ... f(ast_i2, loop_j2) ... && 
				Proposition clos = asm;
				
				//	((/\ ast_i == ast_i2) => loop_j != loop_j2) &&
				final Proposition aaRacePres_ = aaRacePres;
				final PathVariablePlaceholder li = getLoopArgument(l);
				final Assignable<?> lia = li.getAssignable();
				final Version<? extends PathVariable> li1 = ThreadPrivateVersion.fromThread1(lia, l, null),
						li2 = ThreadPrivateVersion.fromThread2(lia, l, null),
						li3 = (Version<PathVariable>) li2.clone();
				final FunctionalVersion fv3 = cloneIfChangeRole(li3.getThreadRole());
				clos = clos.and(()-> aaRacePres_.imply(()-> li1.equal(li2).not()));
				
				changeRole(li1.getThreadRole());
				li3.setName(li2.getName() + "_1");
				fv3.setArgument(l, li3);
				// 	(f(ast_i, loop_j) = ... f(ast_i2, loop_j2) ... => 
				// 		f(ast_i, loop_j) != f(ast_i, loop_j3) && loop_j != loop_j3)
				clos = clos.and(()-> asm.imply(()-> 
				equal(fv3).not().and(li1.equal(li3).not())));
				
				//	forall lb <= (ast_i, ast_i2, loop_j, loop_j2, loop_j3) <= ub, clos
				final ArithmeticExpression[] bs = ASTLoopUtil.getBoundsOf(l);
				final ArithmeticExpression lb = bs[0], ub = bs[1];
				final List<ExpressionRange<? extends Expression>> arClos = new ArrayList<>(getArgumentRanges(l));
				arClos.add((ExpressionRange<? extends Expression>) ExpressionRange.from(li, lb, ub));
				for (ArithmeticExpression saa : sa.getArguments()) {
					final Expression saae = saa.toExpression();
					if (!tests(saae.dependsOn(li))) continue;
					arClos.add((ExpressionRange<? extends Expression>) ExpressionRange.from(saae, lb, ub));
				}
				arClos.add((ExpressionRange<? extends Expression>) ExpressionRange.from(sa.getLoopArgument(l), lb, ub));
				
				// Post condition
				//	forall lb <= (ast_i) <= ub, loop_j > ub, f(ast_i, loop_j) = fpost(ast_i)
				final Proposition lRace = sa.toTrinity(l, Forall.from(arClos, clos));
				race = race == null ? lRace : race.andSkipNull(lRace);
				if (race != null) OmpDirective.fromEnclosing(l, getCondGen()).addRaceAssertion(race);
				
			} catch (NoSuchVersionException e) {
				throwTodoException(e);
			}
		}
		return race;
	}
	
	@Override
	public Proposition toProposition() {
		Proposition prop = null;
		if (tests(isAssigned())) prop = toTrinity();
		else for (Assignable<?> asd : getAssigneds()) {
			final Proposition asdProp = toTrinity(asd.getFirstAssignment().toEquality());
			prop = prop == null ? asdProp : prop.and(asdProp);
		} 
	
		if (isPrivate()) prop = prop.andSkipNull(generateRaceAssertion());
		return prop != null ? 
				prop : throwNullArgumentException("trinity");
	}

	@SuppressWarnings("unchecked")
	private Proposition toPrecondition(IASTStatement loop) {
		assert getLoops().contains(loop);
		final Assignable<?> preFv = getAdjacentAssignable().previousAssigned();
		if (preFv != null && !tests(preFv.isDirectlyFunctional())) {
			final List<ExpressionRange<? extends Expression>> arlb = new ArrayList<>(getArgumentRanges(loop));
			arlb.add((ExpressionRange<? extends Expression>) 
					ExpressionRange.from(getLoopArgument(loop), null, ASTLoopUtil.getLowerBoundOf(loop)));
			return Forall.from(arlb, equal(preFv.getVersion()));
		}
		return null;
	}
	
	@SuppressWarnings("unchecked")
	private Proposition toPostcondition(IASTStatement loop) {
		assert getLoops().contains(loop);
		final Assignable<?> postFv = getAdjacentAssignable().nextLocallyAssigned();
		if (postFv != null && !tests(postFv.isDirectlyFunctional())) {
			final List<ExpressionRange<? extends Expression>> arub = new ArrayList<>(getArgumentRanges(loop));
			arub.add((ExpressionRange<? extends Expression>) 
					ExpressionRange.from(getLoopArgument(loop), ASTLoopUtil.getUpperBoundOf(loop), null));
			return Forall.from(arub, equal(postFv.getVersion()));
		}
		return null;
	}
	
	private Proposition toTrinity() {
		final VersionEnumerable<FunctionalPathVariable> addr = getAddress();
		return toTrinity(Equality.from(
				getFuncCallView(), 
				addr.getAssigner()));
	}
	
	private Proposition toTrinity(Proposition closure) {
		Proposition prop = null;
		for (IASTStatement loop : getLoops()) {
			final Proposition loopProp = 
					toTrinity(loop, Forall.from(Collections.singleton(getLoopArgument(loop)), closure));
			prop = prop == null ? loopProp : prop.and(loopProp);
		}
		return prop;
	}
	
	private Proposition toTrinity(IASTStatement loop, Proposition closure) {
		assert closure != null;
		final Proposition pre = toPrecondition(loop);
		final Proposition post = toPostcondition(loop);
		if (pre != null) closure = closure.and(pre);
		if (post != null) closure = closure.and(post);
		return closure;
	}
	
	
	
//	@Override
//	public String disambiguateString(SerialFormat format, 
//			String originalTerm, String disambiguousTerm) {
//		return format == null 
//				? super.disambiguateString(format, originalTerm + "(", disambiguousTerm)
//				: super.disambiguateString(format, originalTerm, disambiguousTerm);
//	}
	
	
	
	@Override
	protected String toNonEmptyString(boolean usesParenthesesAlready) {
		return getFuncCallView().toNonEmptyString();
	}

	@Override
	public String toZ3SmtCodomainType() {
		return get(()-> getFunction().getType().toZ3SmtString(true, false),
				e-> throwTodoException(e));
	}

	@Override
	public String toZ3SmtNameDeclaration() {
		return get(()-> getFunction().getName(),
				()-> getID(SerialFormat.Z3_SMT));	// isLoopIterator() 
	}
	
	@Override
	public String toZ3SmtTypeDeclaration() {
		return "(" + toZ3SmtLocalParamsDeclaration(false) +") "
				+ (isLoopIterator() ? toZ3SmtType() : toZ3SmtCodomainType()); 
	}
	
	@Override
	public String toZ3SmtLocalParamsDeclaration(boolean printsParamNames) {
		return isArgument() 
				? ""											// for functional array arguments
				: super.toZ3SmtLocalParamsDeclaration(printsParamNames);	// for functional arrays
	}

	/* (non-Javadoc)
	 * @see ompca.condition.ConditionElement#toZ3SmtString()
	 */
	@Override
	public String toZ3SmtString(
			boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs) {
		checkUbiquitous();
		return printsVariableDeclaration || isArgument() 
				// declaration and getting ID are handled by Version generally
				? super.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition, isLhs)	
				: getFuncCallView().toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition, isLhs);
	}

}