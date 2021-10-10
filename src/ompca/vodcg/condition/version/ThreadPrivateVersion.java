/**
 * 
 */
package ompca.vodcg.condition.version;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.DuoKeyMap;
import ompca.vodcg.Assignable;
import ompca.vodcg.FunctionalAssignable;
import ompca.vodcg.SystemElement;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.ConditionElement;
import ompca.vodcg.condition.FunctionalPathVariable;
import ompca.vodcg.condition.ParallelCondition;
import ompca.vodcg.condition.PathVariable;
import ompca.vodcg.condition.PathVariablePlaceholder;
import ompca.vodcg.condition.Referenceable;
import ompca.vodcg.condition.Variable;
import ompca.vodcg.condition.VariablePlaceholder;
import ompca.vodcg.condition.data.ArrayPointer;
import ompca.vodcg.condition.data.ArrayType;
import ompca.vodcg.condition.data.Int;
import ompca.vodcg.condition.version.ThreadRole.ExtendedRole;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class ThreadPrivateVersion<Subject extends Referenceable> 
extends Version<Subject> {

//	public static class PvPrivateDelegate extends PathVariableDelegate {
//
//		/**
//		 * @param lv
//		 * @param initialVersion
//		 * @throws CoreException
//		 * @throws InterruptedException
//		 */
//		private PvPrivateDelegate(
//				LValue lv, ThreadPrivateVersion<FunctionalPathVariable> initialVersion)
//				throws CoreException, InterruptedException {
//			super(lv, initialVersion);
//		}
//	}
	

	
//	private static final 
//	DuoKeyMap<Addressable, FunctionallableRole, Version<?>> 
//	TPV_REGISTRY = new DuoKeyMap<>();
	
	/**
	 * Positive numbers and zero indicate thread ID's; 
	 * while negative ones indicate {@link ThreadRole}'s.
	 */
//	private static final DuoKeyMap<LValue, Integer, PvPrivateDelegate> 
//	FUNCTIONAL_DELEGATES = new DuoKeyMap<>();
	private static final DuoKeyMap<FunctionalAssignable, ExtendedRole, ThreadPrivateVersion<FunctionalPathVariable>> 
	FUNCTIONAL_TPV_REGISTRY = new DuoKeyMap<>();

	

	private IASTStatement astScope;
	
	private ThreadPrivateVersion(IASTStatement block, VersionEnumerable<Subject> addr, 
			FunctionallableRole role) throws NoSuchVersionException {
		super(addr, role);
		init(block, addr, role);
	}
	
	private ThreadPrivateVersion(IASTStatement block, VersionEnumerable<Subject> addr, Subject sbj,
			FunctionallableRole role) throws NoSuchVersionException {
		super(addr, sbj, role);
		init(block, addr, role);
	}
	
//	@SuppressWarnings("unchecked")
//	@Override
//	protected Object cloneNonConstant() {
//		ThreadPrivateVersion<Subject> clone = (ThreadPrivateVersion<Subject>) super.cloneNonConstant();
//		clone.astScope = (IASTStatement) clone.astScope;
//		return clone;
//	}
	
	private void init(IASTStatement block, VersionEnumerable<Subject> addr, ThreadRoleMatchable role) {
		if ((block = initPrivatizingBlock(block)) == null) throwNullArgumentException("block");
//		if (!(block instanceof IASTForStatement)) throwTodoException("unsupported block");
		astScope = block;

		if (addr instanceof Assignable && role instanceof ExtendedRole) 
			consume(t-> setType(t),
					()-> ArrayType.from((Assignable<?>) addr, (ExtendedRole) role),
					e-> throwTodoException("unsupported functional private", e));
	}
	
	private IASTStatement initPrivatizingBlock(IASTStatement block) {
		return block != null
				? block 
				: getAssignable().getPrivatizingBlock();
	}
	
	
	
//	@SuppressWarnings("unchecked")
//	private static <Subject extends Referenceable> 
//	ThreadPrivateVersion<Subject> from(
//			VersionEnumerable<Subject> addr, ThreadRole role, 
//			TrySupplier<ThreadPrivateVersion<Subject>, NoSuchVersionException> sup) {
//		if (addr == null) throwNullArgumentException("assignable");
//		if (role == null) throwNullArgumentException("role");
//
//		ThreadPrivateVersion<Subject> ver = getNonException(()-> 
//		(ThreadPrivateVersion<Subject>) TPV_REGISTRY.get(addr, role));
//		if (ver == null) try {
//			// including blockStat UniversalVersion -> ThreadPrivateVersion 
//			TPV_REGISTRY.put(addr, role, ver = 
//					(ThreadPrivateVersion<Subject>) fromSuperversion(addr, role, sup));
//			
//		} catch (NoSuchVersionException e) {
//			throwTodoException(e);
//		}
//		return ver;
//	}
	
	public static Version<Variable> from(
			Variable v, IASTStatement blockStat, ThreadRole role, Boolean isGlobal) 
					throws IllegalArgumentException, NoSuchVersionException {
		if (v instanceof PathVariable) 
			throwInvalidityException("only for non-AST variables");
		
		@SuppressWarnings("unchecked")
		final VariablePlaceholder<Variable> vp = 
		(VariablePlaceholder<Variable>) VariablePlaceholder.fromNonAST(v, isGlobal);
//		vp.setConstant(null);
		return from(vp, role, 
				()-> new ThreadPrivateVersion<>(blockStat, vp, v, role));
	}
	
	public static <Subject extends Referenceable> Version<Subject> from(
			VersionEnumerable<Subject> addr, Subject sbj, IASTStatement blockStat, ThreadRole role) 
					throws IllegalArgumentException, NoSuchVersionException {
		return from(addr, role, 
				()-> new ThreadPrivateVersion<>(blockStat, addr, sbj, role));
	}
	
	/**
	 * @param asn
	 * @return
	 * @throws NoSuchVersionException 
	 */
	public static Version<? extends PathVariable> from(Assignable<?> asn) 
			throws NoSuchVersionException {
		if (asn == null) throwNullArgumentException("assignable");

		asn = (Assignable<?>) asn.previousOrUnambiguousAssigned();
		try {
			final List<ArithmeticExpression> args = asn.getFunctionalArguments();
			if (asn.isLoopConditional()) return fromFunctional(
					(FunctionalAssignable) asn, null, ThreadRole.FUNCTION.extend(args));
			
			fromThread2(asn, null, args);
			return fromThread1(asn, null, args);
			
		} catch (NoSuchVersionException e) {
			throw e;
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	
	@SuppressWarnings("unchecked")
	public static ThreadPrivateVersion<PathVariable> from(Assignable<PathVariable> asn, 
			final IASTStatement blockStat, final FunctionallableRole role) 
					throws NoSuchVersionException {
		final Assignable<PathVariable> asn_ = 
				(Assignable<PathVariable>) checkThreadPrivatePre(asn, role);
		return asn_.debugGet(()-> (ThreadPrivateVersion<PathVariable>) 
				from(asn_, role.getBasic(), ()-> new ThreadPrivateVersion<>(blockStat, asn_, role)));
	}
	
	public static Version<? extends PathVariable> fromThread1(Assignable<?> asn, 
			IASTStatement blockStat, List<ArithmeticExpression> args) 
					throws NoSuchVersionException {
		return fromThreadRole(asn, blockStat, args, ThreadRole.THREAD1);
	}
	
	public static Version<? extends PathVariable> fromThread2(Assignable<?> asn, 
			IASTStatement blockStat, List<ArithmeticExpression> args) 
					throws NoSuchVersionException {
		return fromThreadRole(asn, blockStat, args, ThreadRole.THREAD2);
	}
	
	@SuppressWarnings("unchecked")
	public static Version<? extends PathVariable> fromThreadRole(Assignable<?> asn, 
			IASTStatement blockStat, List<ArithmeticExpression> astArgs, FunctionallableRole role) 
					throws NoSuchVersionException {
		asn = checkThreadPrivatePre(asn, role);
		
		final ThreadRole r = role instanceof ThreadRole ? (ThreadRole) role : null;
		final ExtendedRole er = role instanceof ExtendedRole ? (ExtendedRole) role : null;
		if (r == null && er == null) role.throwUnsupportedRoleException();
		
		if (asn.isLoopIterator()) return fromFunctional(asn, blockStat, er != null ? er : r.extend(asn.toFunctional()));
		if (astArgs == null || astArgs.isEmpty()) {
			if (asn.isArray()) astArgs = ((ArrayPointer) asn.getEnclosingArray()).getArguments();
		}
		return astArgs != null && !astArgs.isEmpty()
				? fromFunctional(asn, blockStat, er != null ? er : r.extend(astArgs))
				: from((Assignable<PathVariable>) asn, blockStat, role);
	}
	
//	/**
//	 * @param asn
//	 * @param blockStat
//	 * @param role
//	 * @return
//	 * @throws NoSuchVersionException 
//	 */
//	public static Version<FunctionalPathVariable> fromFunctional(
//			Assignable<?> asn, IASTStatement blockStat, ExtendedRole role) 
//					throws NoSuchVersionException {
//		asn = checkThreadPrivatePre(asn, role);
//		
//		final int roleId = -(role.getBasic().ordinal() + 1);
//		assert roleId < 0;
//		return fromFunctional(asn, blockStat, roleId, role);
//	}
	
	/**
	 * Finding some functional private variable delegate.
	 * Only a path variable can be functionalized.
	 * 
	 * @param asn
	 * @param blockStat
	 * @param threadId - negative value means in various (non-constant) thread ID's.
	 * 	For various thread role cases please use 
	 * 	{@link #fromFunctional(Assignable, IASTStatement, ThreadRole, ParallelCondition)}.
	 * @return
	 * @throws NoSuchVersionException 
	 */
	public static Version<FunctionalPathVariable> fromFunctional(
			final FunctionalAssignable asn, final IASTStatement blockStat, final int threadId, final ParallelCondition pc) 
					throws NoSuchVersionException {
		if (pc == null) throwNullArgumentException("parallel condition");
		
		final boolean isVariousThread = threadId < 0;
		final ExtendedRole FUNCTION_ROLE = ThreadRole.FUNCTION.extend(
				Arrays.asList(isVariousThread ? pc.getThread(ThreadRole.FUNCTION) : Int.from(threadId, null)));
		final int FUNCTION_ROLE_ID = -(FUNCTION_ROLE.getBasic().ordinal() + 1);
//		if (isVariousThread) 
//			VOPCondGen.throwTodoException("Negative thread ID:" + lv.getName() + "(t) !");
		assert FUNCTION_ROLE_ID < 0;
		return fromFunctional(
				asn, 
				blockStat, 
//				isVariousThread ? FUNCTION_ROLE_ID : threadId, 
				FUNCTION_ROLE);
	}
	
	public static Version<FunctionalPathVariable> fromFunctional(
			Assignable<?> asn, IASTStatement blockStat, ExtendedRole role) 
					throws NoSuchVersionException {
		final FunctionalAssignable fasn = asn.toFunctional();
		Version<FunctionalPathVariable> ver = FUNCTIONAL_TPV_REGISTRY.get(fasn, role);
		if (ver != null) return ver;
		
		try {
		if (blockStat == null) {
			blockStat = asn.getPrivatizingBlock();
			if (blockStat == null) return throwNoSuchVersionException(asn, "non-thread-private");
		}
			
		final IASTStatement blockStat_ = blockStat;
		ver = fromSuperversion(fasn, role, ()-> new ThreadPrivateVersion<>(blockStat_, fasn, role));
		if (asn.isLoopIteratingIterator()) {
			// TODO? FunctionalIntInputVersion.from(lv, args)) for loop iterators
		
		} else if (blockStat instanceof IASTForStatement) {
			final IASTForStatement forStat = (IASTForStatement) blockStat;
			@SuppressWarnings("unchecked")
			final FunctionalVersion subVer = (FunctionalVersion) FunctionalVersion.from(
					(Assignable<PathVariable>) asn, role, Arrays.asList(forStat));
			subVer.setArguments(role.getArguments());
			ver.subversion((Version<? extends FunctionalPathVariable>) subVer);
		
		} else throwTodoException("private functional assignable's with private arguments");

		final VariablePlaceholder<PathVariable> pd = PathVariablePlaceholder.from(asn);
		pd.reversion(ver);
//		if (!(pd.getVersion() instanceof ThreadPrivateVersion<?>)) 
//			Debug.throwTodoException("pd.reversion(ver)?");
			FUNCTIONAL_TPV_REGISTRY.put(fasn, role, (ThreadPrivateVersion<FunctionalPathVariable>) ver);
		} catch (ClassCastException e) {
			throwTodoException(e);
		}
		return ver;
	}

	
	
	private static Assignable<?> checkThreadPrivatePre(final Assignable<?> asn, final FunctionallableRole role) 
			throws NoSuchVersionException {
		if (asn == null) throwNullArgumentException("assignable");
		if (role == null) throwNullArgumentException("role");
		
		if (!role.equalsBasic(ThreadRole.THREAD1) && !role.equalsBasic(ThreadRole.THREAD2))
//			&& !role.equals(ThreadRole.FUNCTION))
		throwNoSuchVersionException(asn, "unsupported role");
//		if (role.equals(ThreadRole.FUNCTION)) 
//			throwNoSuchVersionException(asn, "function role should NOT be thread-private");

		if (!asn.isThreadPrivate()) {
			if (tests(asn.isConstant())) 
				throwNoSuchVersionException(asn, "shared constants need not to be thread-private");
			throwNoSuchVersionException(asn, "non-thread-private");
		}
		if (tests(asn.isFunctional())) return asn;
		
		// isAssigned == null || !isAssigned
		final Set<? extends Assignable<?>> asds = asn.getAssigneds();
		if (asds.isEmpty()) return asn.getDeclared();
		
		// size >= 1, multiple assigned's mean loop assigned's 
		// asn.isThreadPrivate
		for (Assignable<?> asd : asds) if (asd.isThreadPrivate()) try {
			return asd;
		} catch (ClassCastException e) {
			throwUnhandledException(e);
		}
		return throwNoSuchVersionException(asn, asn + " has no thread-private assigneds");
	}
	

	
	@SuppressWarnings("unchecked")
	@Override
	public <T extends ConditionElement> T cloneIfChangeRole(final FunctionallableRole role) {
		try {
			return super.cloneIfChangeRole(role);
			
		} catch (NoSuchVersionException e) {
			if (isInAST()) return role instanceof FunctionallableRole
					? (T) from((Assignable<PathVariable>) getAssignable(), getBlock(), (FunctionallableRole) role)
					: throwTodoException("unsupported role");
			else return role instanceof ThreadRole
					? (T) from((Variable) getSubject(), getBlock(), (ThreadRole) role, isGlobal())
					: throwTodoException("unsupported role");
			
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}

	
	
	public IASTStatement getBlock() {
		return astScope;
	}
	
//	public ThreadRole getRole() {
//		final ThreadRoleMatchable tr = getThreadRole();
//		return tr instanceof FunctionallableRole
//				? ((FunctionallableRole) tr).getBasic()
//				: throwTodoException("unsupported role");
//	}

//	@Override
//	public PlatformType getType() {
//		return getReferenceableType();
//	}
	


//	@Override
//	protected <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType) {
//		switch (getRole()) {
//		case FUNCTION:	
//			Version<Subject> sub = getSubversion();
//			if (sub != null) // VOPCondGen.throwInvalidityException("FUNCTION role with null function?");
//				return sub.cacheDirectVariableReferences(refType);
//			
//		case MASTER:
//		case NON_MASTER:
//		case THREAD1:
//		case THREAD2:
//		default:
//		}
//		return super.cacheDirectVariableReferences(refType);
//	}

	
	
	@Override
	public boolean isThreadPrivate() {
		return true;
	}

	/* (non-Javadoc)
	 * @see ompca.condition.Version#equals(ompca.condition.Version)
	 */
	@SuppressWarnings("unchecked")
	@Override
	protected boolean equalsToCache(SystemElement e2) {
		assert astScope != null;
		return super.equalsToCache(e2) 
				&& astScope.equals(((ThreadPrivateVersion<Subject>)e2).astScope);
	}

	protected List<Integer> hashCodeVars() {
		assert astScope != null;
		final List<Integer> vars = new ArrayList<>(super.hashCodeVars());
		vars.add(astScope.hashCode());
		return vars;
	}

	
	
//	/**
//	 * For both {@link FunctionalVersion}'s identical name is the <em>only</em> 
//	 * derivation constraint.
//	 *  
//	 * @param newVer
//	 * @return
//	 */
//	@Override
//	protected boolean derives(Version<?> newVer) {
//		if (newVer instanceof FunctionalVersion) {
//			final String sbjName = getSubject().getName();
//			if (sbjName == null || sbjName.isEmpty()) 
//				throwNullArgumentException("subject name");
//			return sbjName.equals(newVer.getSubject().getName());
//		}
//		return super.derives(newVer);
//	}

	/* (non-Javadoc)
	 * @see ompca.condition.version.Version#matches(ompca.condition.version.ThreadPrivateVersion.ThreadRole)
	 */
	@Override
	public boolean matches(ThreadRoleMatchable newRole) {
		if (newRole != null && newRole instanceof FunctionallableRole) 
			switch (((FunctionallableRole) newRole).getBasic()) {
			case FUNCTION:
			case THREAD1:
			case THREAD2:		return super.matches(newRole);
			case MASTER:
			case NON_MASTER:
			default:
			}
		return false;
	}

	
	
	@Override
	public String toZ3SmtString(boolean printsVariableDeclaration, 
			boolean printsFunctionDefinition, boolean isLhs) {
		final Version<Subject> sub = getSubversion();
		if (sub != null) 
			return sub.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition, isLhs);
//		else if (getThreadRole().isFunctional()) 
//			throwTodoException("functional role w/o function?");
		
		return super.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition, isLhs);
	}
	
}