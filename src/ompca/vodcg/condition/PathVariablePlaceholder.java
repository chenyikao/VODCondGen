/**
 * 
 */
package ompca.vodcg.condition;

import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.NavigableSet;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.function.Supplier;

import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNameOwner;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IBinding;
import org.eclipse.cdt.core.dom.ast.IVariable;

import ompca.Elemental;
import ompca.vodcg.ASTAddressable;
import ompca.vodcg.ASTException;
import ompca.vodcg.ASTUtil;
import ompca.vodcg.Assignable;
import ompca.vodcg.FunctionalAssignable;
import ompca.vodcg.IncomparableException;
import ompca.vodcg.ReenterException;
import ompca.vodcg.SystemElement;
import ompca.vodcg.UncertainException;
import ompca.vodcg.UncertainPlaceholderException;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.version.ArrayAccessVersion;
import ompca.vodcg.condition.version.ConstArrayDeclaration;
import ompca.vodcg.condition.version.EnumeratedVersion;
import ompca.vodcg.condition.version.FunctionalVersion;
import ompca.vodcg.condition.version.FunctionallableRole;
import ompca.vodcg.condition.version.MutexAssignedVersion;
import ompca.vodcg.condition.version.NoSuchVersionException;
import ompca.vodcg.condition.version.ThreadPrivateVersion;
import ompca.vodcg.condition.version.ThreadRole;
import ompca.vodcg.condition.version.ThreadRoleMatchable;
import ompca.vodcg.condition.version.UniversalVersion;
import ompca.vodcg.condition.version.Version;
import ompca.vodcg.parallel.OmpDirective;
import ompca.vodcg.parallel.OmpThreadPrivatizable;

/**
 * A constant {@link Version} access interface for the {@link Variable} references 
 * used in an {@link Expression}. Therefore the subject variable may change from 
 * {@link PathVariable} to {@link FunctionalPathVariable} without the reconstruction of
 * this expression element.
 * 
 * A path variable placeholder maps to an assignable, no matter it's assigned or assigning.
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class PathVariablePlaceholder 
extends VariablePlaceholder<PathVariable>
implements Comparable<PathVariablePlaceholder>, Comparator<PathVariablePlaceholder> {

	static private final Method METHOD_CACHE_SCOPE = 
			Elemental.getMethod(PathVariablePlaceholder.class, "cacheScope");
//	private static final Method METHOD_GET_THREAD_ROLE = 
//			Elemental.getMethod(PathVariablePlaceholder.class, "getThreadRole");
//	static private final Method METHOD_GET_VARIABLE_REFERENCES = 
//			Elemental.getMethod(PathVariablePlaceholder.class, "getVariableReferences");
	static private final Method METHOD_GET_VERSION = 
			Elemental.getMethod(PathVariablePlaceholder.class, "getVersion");
	static private final Method METHOD_DETERMINE_VERSION = 
			Elemental.getMethod(PathVariablePlaceholder.class, "determineASTVersion", Assignable.class, IASTStatement.class, FunctionallableRole.class, Version.class);
//	static private final Method METHOD_FROM = 
//			Elemental.getMethod(PathVariablePlaceholder.class, "from", Assignable.class);
//	static private final Method METHOD_TO_PROPOSITION = 
//			Elemental.getMethod(PathVariablePlaceholder.class, "toProposition");
	static private final Method METHOD_TO_NON_EMPTY_STRING = 
			Elemental.getMethod(PathVariablePlaceholder.class, "toNonEmptyString", boolean.class);

	private static final Map<Assignable<?>, PathVariablePlaceholder> 
	AST_PV_PLACEHOLDERS = new HashMap<>();

	/**
	 * <em>Only for</em> path variable assignable's.
	 */
	private Assignable<?> asn = null;

	private Runnable reversioning = null;
	private Supplier<Boolean>[] reversionConditions = null;

		
	
	/**
	 * @param asn
	 * @param initialVersion can't be null.
	 * @throws NoSuchVersionException 
	 */
	@SuppressWarnings("unchecked")
	private PathVariablePlaceholder(
			Assignable<?> asn, Version<? extends PathVariable> initialVersion) 
					throws ASTException, IncomparableException, UncertainPlaceholderException {
		super((Version<PathVariable>) determineASTVersion(asn, asn.getPrivatizingBlock(), initialVersion.peekRole(), initialVersion), 
				true, asn.isGlobal(), asn.isAssigned(), asn.getAssigner());
		init(asn);
	}

	private PathVariablePlaceholder(Assignable<?> asn, Function<Reference<Version<? extends PathVariable>>, Version<? extends PathVariable>> verSup) {
		super(asn.getName(), verSup, true, asn.isGlobal(), asn.getCondGen());
		init(asn);
	}
	
	private void init(Assignable<?> asn) {
		assert asn != null;
		
		if (asn.isASTFunction()) throwTodoException("unsupported assignable type");
//		if (tests(asn.isAssigned())) setAssigner(asn.getAssigner());

		this.asn = asn;
//		setName(asn.getName());
		AST_PV_PLACEHOLDERS.put(asn, this);
	}
	
	
	
	/**
	 * For sub-classes, such as {@link MutexAssignedVersion}, which doesn't assign any default version.
	 * 
	 * Default to enumerated version for easy debugging.
	 * 
	 * @param asn
	 * @param dv - default version
	 * @return
	 * @throws ASTException
	 * @throws IncomparableException
	 * @throws ReenterException - thrown by lambda (version factory methods)
	 * @throws UncertainPlaceholderException
	 */
	@SuppressWarnings("unchecked")
	private static Version<? extends PathVariable> determineASTVersion(
			final Assignable<?> asn, final IASTStatement blockStat, final FunctionallableRole role, final Version<? extends PathVariable> dv) 
					throws ASTException, IncomparableException, 
					UncertainPlaceholderException {
		if (dv instanceof EnumeratedVersion) return dv;
		assert asn != null;
		if (asn.enters(METHOD_DETERMINE_VERSION)) 
			asn.throwUncertainPlaceholderException(METHOD_DETERMINE_VERSION);
		
		/* No previous writing history means immutable or non-initialized pv. 
		 * Or the following placeholder's (assignable's) share the previous version 
		 * regardless of any self-assignment.
		 * 
		 * Such assigned-or-not detection is performed by each version public factory method.
		 */
		try {
			final boolean hasDv = dv != null;
			final FunctionallableRole dr = hasDv ? 
					dv.getThreadRole() : (role != null ? role : asn.initRole());
			
			// initiated version base
			final Version<? extends PathVariable> iv = asn.trySkipException(
					METHOD_DETERMINE_VERSION,
					Arrays.asList(NoSuchVersionException.class, ClassCastException.class),
					()-> dv instanceof ThreadPrivateVersion ? dv : ThreadPrivateVersion.fromThreadRole(asn, blockStat, null, dr),
					()-> dv instanceof ArrayAccessVersion ? dv : ArrayAccessVersion.from((Version<PathVariable>) dv, (Assignable<PathVariable>) asn, dr),
					()-> dv instanceof ConstArrayDeclaration ? dv : ConstArrayDeclaration.from((Assignable<PathVariable>) asn),
					()-> dv instanceof MutexAssignedVersion ? dv : MutexAssignedVersion.from((Assignable<PathVariable>) asn, dr),
					()-> dv instanceof FunctionalVersion ? dv : FunctionalVersion.from(asn, dr, blockStat == null ? null : Arrays.asList(blockStat)),
					()-> dv instanceof EnumeratedVersion ? dv : EnumeratedVersion.from(asn, dr),
					()-> dv instanceof UniversalVersion ? dv : UniversalVersion.from(asn),
					()-> dv
					);
			
			if (iv == null) throwNullArgumentException("initial version");
			if (hasDv) {
				if (iv.derives((ThreadRoleMatchable) dv)) return dv;
				
				if (dv != iv 
						&& !(dv instanceof UniversalVersion)
						&& !dv.derives((ThreadRoleMatchable) iv)) {
					final ThreadRoleMatchable ivr = iv.getThreadRole();
					if (!dv.matches(ivr)) {
						final FunctionallableRole dvr = dv.getThreadRole();
						if (ivr.derives(dvr)) iv.changeRole(dvr);	// ex. FunctionalVersion -> ThreadPrivateVersion
						else throwTodoException("role-unmatching versions");
					}
					((Version<PathVariable>) iv).subversion(dv);
				}
			}
			return iv;
			
		} catch (ReenterException e) {
			throw e;
		} catch (Exception e) {
			return throwUnhandledException(e);
		} 
	}
	
	
	
	/**
	 * Double checking the delegate registry in case of creating the delegate during those preceding condition testings.
	 *  
	 * @param asn
	 * @param version
	 * @return
	 * @throws NoSuchVersionException 
	 */
	private static PathVariablePlaceholder match(
			Assignable<?> asn, Version<? extends PathVariable> version) {
		PathVariablePlaceholder pvp = AST_PV_PLACEHOLDERS.get(asn);
		if (pvp != null && version != null) pvp.reversion(version);
		return pvp;
	}
	
	private static PathVariablePlaceholder matchOrNew(
			Assignable<?> asn, Version<? extends PathVariable> version, 
			TrySupplier<PathVariablePlaceholder, Exception> constructor) 
					throws ASTException, IncomparableException, 
					UncertainPlaceholderException, NoSuchVersionException {
		PathVariablePlaceholder pvp = match(asn, version);
		if (pvp == null) try {
			if (constructor == null) throwNullArgumentException("constructor");
			pvp = Elemental.getThrow(constructor);
			if (version != null) pvp.reversion(version);
			
		} catch (ASTException | IncomparableException
			| UncertainPlaceholderException | NoSuchVersionException e) {
			throw e;
		} catch (Exception e) {
			throwUnhandledException(e);
		}
		return pvp;
	}
	
	
	
	public static PathVariablePlaceholder from(
			IASTExpression exp, final ASTAddressable rtAddr, VODCondGen condGen) 
		throws ASTException, IncomparableException, 
		UncertainPlaceholderException, NoSuchVersionException {
		return from(Assignable.from(exp, rtAddr, condGen));
		
//		final Set<Version<Variable>> vs = Expression.fromRecursively(exp, condGen)
//				.getDirectVariableReferences();
//		if (vs == null || vs.isEmpty()) return null;
//		for (Version<Variable> v : vs) {
//			lv = v.getAssignable();
//			if (lv != null) return from(lv);
//		}
//		return null;
	}

//	public static PathVariableDelegate from(IASTCastExpression exp, 
//			IASTSimpleDeclSpecifier decl, IASTExpression operand, VOPCondGen condGen) {
//		if (exp == null) Debug.throwNullArgumentException("expression");
//		if (decl == null) Debug.throwNullArgumentException("declaration specifier");
//		if (operand == null) Debug.throwNullArgumentException("operand");
//		
//		PathVariableDelegate vd = from(operand, condGen);
//		if (vd == null) return null;	// constant casting
//		
//		@SuppressWarnings("unchecked")
//		Version<PathVariable> oldV = (Version<PathVariable>) vd.getVersion();
//		if (!(oldV instanceof CastVersion)) {
//			CastVersion<PathVariable> newV = new CastVersion<>(
//					(PathVariable) vd.getVariable(), decl, ThreadRole.MASTER);
//			newV.subversion(oldV);
//			vd.setVersion(newV);
//		}
//		return vd;
//	}

	/**
	 * @param declarator
	 * @param condGen
	 * @return
	 */
	public static PathVariablePlaceholder from(IASTDeclarator declarator, final ASTAddressable rtAddr, VODCondGen condGen) 
		throws ASTException, IncomparableException, 
		UncertainPlaceholderException, NoSuchVersionException {
		return from(Assignable.from(declarator, rtAddr, condGen));
	}
	
	/**
	 * @param var
	 * @param scope - pre-cached function scope for some function parameter var
	 * @param condGen 
	 * @return
	 */
	public static PathVariablePlaceholder from(
			IVariable var, ompca.vodcg.condition.Function scope, VODCondGen condGen) 
					throws ASTException, IncomparableException, 
					UncertainPlaceholderException, NoSuchVersionException {
		if (scope == null) throwNullArgumentException("function scope");
		
		final IASTName varAst = ASTUtil.getNameOfFrom(var, scope.getIName());
		// var != null && varAst == null => var is in external libraries
		return varAst == null 
				? from(Assignable.from(var, condGen)) 
				: from(Assignable.from(varAst, scope.getRuntimeAddress(), condGen));
	}
	
	/**
	 * @param varBind
	 * @param varName
	 * @param varNameOwner
	 * @param condGen
	 * @return null if missing bounded assignable's
	 * @throws ASTException
	 */
	public static PathVariablePlaceholder from(IBinding varBind, 
			IASTName varName, IASTNameOwner varNameOwner, final ASTAddressable rtAddr, VODCondGen condGen) 
					throws ASTException {
		try {
			return applySkipNullThrow(asn-> from(asn), ()-> 
			Assignable.from(varBind, varName, varNameOwner, rtAddr, condGen));
			
		} catch (ASTException e) {	// assignable may be un-resolvable!
			return ASTUtil.throwASTException(varBind, e);
		} catch (Exception e) {
//			if (isUncertainPlaceholderException(e)) throw (IllegalStateException) e;
			return throwUnhandledException(e);
		}
	}

	public static PathVariablePlaceholder from(Assignable<?> asn) {
		return from(asn, null, null);
	}
	
//	public static PathVariablePlaceholder from(Assignable asn, 
//			Version<? extends PathVariable> version) {
//		return from(asn, version, null);
//	}
	
	/**
	 * @param asn - assumed not assigned
	 * @param version - null means inheriting the version of previous assignable or 
	 * 	default one
	 * @param verSup
	 * @return an inherited version delegate without assignment-caused reversion, 
	 * 	or an existing delegate if available given null version.
	 */
	private static PathVariablePlaceholder from(Assignable<?> asn, 
			Version<? extends PathVariable> version, Function<Reference<Version<? extends PathVariable>>, Version<? extends PathVariable>> verSup) {
		if (asn == null) throwNullArgumentException("assignable");
//		if (asn.isFunction()) throwNullArgumentException("path variable assignable");
//		if (asn.enters(METHOD_FROM)) {
////			if (version != null) throwTodoException("un-handled version initialization");
//			asn.throwUncertainPlaceholderException(METHOD_FROM);
//		}
		
//		asn.enter(METHOD_FROM);
		PathVariablePlaceholder vd = null;
		try {
		vd = match(asn, version);
		if (vd != null) return vd;	//asn.leave(METHOD_FROM, vd);

		// vd == null
		if (version != null) vd = matchOrNew(
				asn, version, ()-> new PathVariablePlaceholder(asn, version));
		else if (verSup != null) vd = matchOrNew(
				asn, version, ()-> new PathVariablePlaceholder(asn, verSup));
//		else if (!Elemental.tests(asn.isDirectlyFunctional()) && !Elemental.tests(asn.isConstant())) {	// !isConstant || isConstant == null
			// loop initialized iterator may be both constant and functional
//			if (asn.isLoopInitializedIterator()) vd = fromCanonicalInitializedIteratorOf(loop, condGen);
//			else if (asn.isLoopIterator()) vd = fromCanonicalIteratorOf(asn, loop);
		
		// conditional placeholder version is NOT yet ready
//		else if (!asn.isLoopIterator() && !asn.isDirectlyConditional() && Elemental.testsNot(asn.isAssigned())) 
//			vd = Elemental.applySkipNull(pAsn-> from(pAsn, version, verSup), ()-> asn.previousRuntimeAssigned());
//		
//		} catch (ASTException | IncomparableException | ReenterException
//			| UncertainPlaceholderException | NoSuchVersionException e) {
//			throw e;	// thrown by recursive initialization
		} catch (Exception e) {
			throwUnhandledException(e);
//			asn.throwUnhandledException(e, METHOD_FROM);
		}
		
		// version == null
		if (vd == null) vd = new PathVariablePlaceholder(
				asn, addr-> determineASTVersion(asn, null, null, version));
//			vd = matchOrNew(asn, version, ()-> new PathVariableDelegate(asn, (Version<? extends PathVariable>) null));
		return vd;	//asn.leave(METHOD_FROM, vd);
	}
	
	private static PathVariablePlaceholder fromCanonicalIteratorOf(
			Assignable<?> it, IASTForStatement loop) 
					throws ASTException, IncomparableException, 
					UncertainPlaceholderException, NoSuchVersionException {
		return from(it, null, addr-> determineASTVersion(it, loop, null, null));
//		TODO? return MutexAssignedVersion.from(...);
//		TODO? return from(it, null, FunctionalIntInputVersion.from(it, loop));
	}
	
	public static PathVariablePlaceholder fromCanonicalIteratorOf(
			IASTForStatement loop, final ASTAddressable rtAddr, VODCondGen condGen) 
					throws ASTException, IncomparableException, 
					UncertainPlaceholderException, NoSuchVersionException {
		return fromCanonicalIteratorOf(
				Assignable.fromCanonicalIteratorOf(loop, rtAddr, condGen), loop);
	}
	
//	public static PathVariableDelegate fromCanonicalInitializedIteratorOf(IASTForStatement loop, VOPCondGen condGen) {
//		return fromCanonicalIteratorOf(Assignable.fromCanonicalInitializedIteratorOf(loop, condGen), loop);
//	}

	
	
	/**
	 * A path-variable placeholder is one-one mapped to an assignable 
	 * and NOT clone-able.
	 */
	@Override
	protected Object cloneNonConstant() {
		return this;
	}
	
//	/**
//	 * @param pv
//	 * @return sorted but non-guaranteed complete delegates
//	 */
//	private static SortedSet<PathVariableDelegate> sortOnesFor(PathVariable pv) {
//		if (pv == null) return null;
//		
//		SortedSet<PathVariableDelegate> sortedVds = null;
//		for (PathVariableDelegate vd : getOnesFor(pv)) {
//			if (sortedVds == null) sortedVds = new TreeSet<>(vd);
////				if (sortedVds == null) sortedVds = 
////						Collections.synchronizedSortedSet(new TreeSet<>(vd));
//			try {
//				sortedVds.add(vd);
//			} catch (Exception e) {
//				Debug.throwInvalidityException(e.getMessage());
//			}
//		}
//		
//		return sortedVds;
//	}
	
//	/**
//	 * @param pv
//	 * @return non-guaranteed complete delegates
//	 */
//	private static <PV extends PathVariable> Set<PathVariableDelegate> 
//	getOnesFor(PV pv) {
////		assert PATH_VAR_DELEGATES.containsValue(??);
//		if (pv == null) return null;
//		
//		Set<PathVariableDelegate> pvds = new HashSet<>();
//		/* 
//		 * in case of equivalent but different objects of FunctionalPathVariable
//		 * and avoiding {@link ConcurrentModificationException}
//		 */
//		for (PathVariableDelegate d : new ArrayList<>(AST_PV_PLACEHOLDERS.values()))
//			if (d.equalsVariable(pv)) pvds.add(d);
////		for (int i = 0; i < ds.size(); i++) {
////			PathVariableDelegate d = ds.get(i);
////			if (d.equalsVariable(pv)) pvds.add(d);
////		}
//		return pvds;
//	}
	
//	public static PathVariableDelegate get(Assignable ov) {
//		if (ov == null) throwNullArgumentException("assignable");
//		
//		return AST_PV_PLACEHOLDERS.get(ov);
//	}
	
	
	
	@Override
	public IASTStatement getPrivatizingBlock() {
		try {
			for (OmpDirective dir : debugCallDepth(()-> getAssignable().getEnclosingDirectives())) 
				if (dir instanceof OmpThreadPrivatizable) 
					for (PathVariablePlaceholder ppvp : 
						((OmpThreadPrivatizable) dir).getPrivatizedPlaceholders())
//						if (tests(pvp.dependsOn(ppvp))) 
						if (this == ppvp) 
							return dir.getStatement();
			
		} catch (Exception e) {
			throwTodoException(e);
		}
		return null;
	}
	
	@Override
	public FunctionallableRole getThreadRole() 
			throws IncomparableException {
		return debugGet(
				()-> peekThreadRole(),
				()-> getAssignable().initRole(),
				e-> throwUnhandledException(e));
//		try {
//			return guardThrow(
//					()-> super.getThreadRole(),
//					// reentered during placeholder (version) initialization
//					()-> getAssignable().initRole(),
//					null,
//					METHOD_GET_THREAD_ROLE);
//			
//		} catch (UncertainPlaceholderException	// thrown during recursive placeholder initialization
//				| IncomparableException e) {
//			throw e;
//		} catch (Exception e) {					// non-this-reenter thrown by super
//			return throwUnhandledException(e);
//		}
	}

	/**
	 * @param blockStat
	 * @param threadId - negative value means in various (non-constant) thread ID's.
	 * @param pc
	 * @return
	 * @throws NoSuchVersionException 
	 */
	public Version<FunctionalPathVariable> getThreadPrivateVersion(
			IASTStatement blockStat, int threadId, ParallelCondition pc) throws NoSuchVersionException {
		return ThreadPrivateVersion.fromFunctional((FunctionalAssignable) getAssignable(), blockStat, threadId, pc);
	}
	

	
	@Override
	public VODCondGen getCondGen() {
		return getAssignable().getCondGen();
	}
	
	
	
//	@SuppressWarnings("unchecked")
//	@Override
//	public <T> Set<? extends T> getDirectVariableReferences(Class<T> refType) {
//		if (refType == null) return throwNullArgumentException(
//				"reference type", ()-> Collections.emptySet());
//		
//		return refType.isInstance(this) 
//				? Collections.singleton((T) this) 
//				: super.getDirectVariableReferences(refType);
//	}

	public PathVariablePlaceholder getArrayEncloser() {
		final Assignable<?> asn = getAssignable();
		if (asn.isArrayArgument()) 
			return getNonException(()-> (PathVariablePlaceholder)
			asn.getEnclosingArray().getBeginningPlaceholder());
		return null;
	}
	
	public PathVariablePlaceholder getEncloser() {
		final PathVariablePlaceholder ae = getArrayEncloser();
		if (ae != null) return ae;
		
		final Assignable<?> asn = getAssignable();
		if (asn.isCallArgument()) 
			return asn.getEnclosingCall().getTopPlaceholder();
		return null;
	}
	
	public IASTForStatement getEnclosingCanonicalLoop() {
		return getAssignable().getEnclosingCanonicalLoop();
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public PathVariable getVariable() {
		return PathVariable.from((Assignable<PathVariable>) getAssignable());
	}
	
//	/**
//	 * @return a non-null set
//	 */
//	@Override
//	public Set<VariablePlaceholder<?>> getVariableReferences() {
//		final Set<VariablePlaceholder<?>> vrs = super.getVariableReferences();
//		if (!enters(METHOD_GET_VARIABLE_REFERENCES)) {
//			enter(METHOD_GET_VARIABLE_REFERENCES);
//			vrs.addAll(getAssigner().getVariableReferences());
//			leave(METHOD_GET_VARIABLE_REFERENCES);
//		}
//		return vrs;
//	}
	

	
	@Override
	public Version<? extends PathVariable> getVersion() 
			throws ReenterException, IncomparableException, UncertainPlaceholderException {
		if (reversioning != null) try {
			debugCallDepth(()-> guardThrow(()-> 
			{run(reversioning, reversionConditions); return null;},
			METHOD_GET_VERSION)); 
		} catch (ReenterException e) {
			throw e;
		} catch (Exception e) {
			throwUnhandledException(e);
		}
		return super.getVersion();
	}
	
	@Override
	public Version<? extends PathVariable> getVersion(FunctionallableRole role) 
			throws ReenterException, IncomparableException, UncertainPlaceholderException {
		final Assignable<?> asn = getAssignable();
		return get(()-> {
			if (isFunctional()) return FunctionalVersion.from(asn, role, getDependentLoops());
			
			if (isArray()) {
				// a_thread1[i_thread1]
				if (asn.isDirectiveLocal()) return super.getVersion(role);	

				// a_master[i_thread1]
				@SuppressWarnings("unchecked")
				ArrayAccessVersion<PathVariable> mv = (ArrayAccessVersion<PathVariable>) determineASTVersion(asn, null, ThreadRole.MASTER, null);
				mv = mv.cloneReversion(null, role, mv);
//				mv.matchArgumentsTo(mv.getArguments(), role);
				return mv;
			}
			
			final Set<PathVariablePlaceholder> asds = getAssigneds();
			if (asds.size() == 1) {
				for (PathVariablePlaceholder asd : asds) 
					if (asd != this) return getNonNull(()-> asd).getVersion(role);
				// asd == this
				return super.getVersion(role);
			}
			// for non-assigned i b/w assigned's i = lb; i <= ub; i++
			if (asn.isLoopIterator()) return getNonNull(()-> asn.nextLocallyAssigned()).getVersion(role);
			
			return throwTodoException("conditional version disjunction");
		},
		e-> {	// NoSuchVersionException
			final Version<? extends PathVariable> ver = determineASTVersion(asn, null, role, null);
			setVersion(ver);
			return ver;
		});
	}
	
	@Override
//	public <T extends Version<? extends PathVariable>> T getVersion(Class<T> type) {
	public <T> T getVersion(Class<T> type) {
		if (type == null) throwNullArgumentException("version type");
		
		tryAAV: try {
		if (type.asSubclass(ArrayAccessVersion.class) != null) break tryAAV; 
		} catch (ClassCastException e) {
			if (getAssigneds().size() > 1) throwTodoException("conditional version disjunction");
			for (PathVariablePlaceholder asd : getAssigneds()) 
				if (asd != null && asd != this) return asd.getVersion(type);
		}
		// for getting ArrayAccessVersion or assigned's version
		return super.getVersion(type); 
	}
	
//	@Override
//	public Collection<Version<? extends PathVariable>> getVersions() {
//		final PathVariablePlaceholder asd = getAssigned();
//		return asd == null || asd == this 
//				? super.getVersions() 
//				: asd.getVersions();
//	}
	
	
	
	@Override
	public void setVersion(Version<? extends PathVariable> newVer) {
		if (newVer == null) throwNullArgumentException("new version");
		
		if (peekVersions().isEmpty()) super.setVersion(newVer);
		else try {
			super.setVersion(newVer); 
		
		} catch (UncertainPlaceholderException e) {	
			// thrown by recursive placeholder initialization calls
			// for consistent assigned's initial and reversion-ed versions
			final Assignable<?> asn = getAssignable();
			final Version<? extends PathVariable> detVer = 
					determineASTVersion(asn, null, newVer.peekRole(), newVer);
			if (detVer.isFunctional() && detVer.isZ3ArrayAccess() 	// not for functional array arguments
					&& asn != detVer.getAssignable()) throwTodoException(
							"inconsistent assignables for a functional version");
			super.setVersion(detVer); 

		} catch (ASTException | IncomparableException | ReenterException e) {	
			throw e;
		} catch (Exception e) {
			throwUnhandledException(e);
		}
	}
	

	
	/** 
	 * Scope is the one of corresponding {@link Assignable}), 
	 * which is different from the one of referenced {@link Version}.
	 * 
	 * A delegate's scope depends on the completion of construction of its 
	 * corresponding variable, as one of the variable's residing expression.
	 *
	 * @see ompca.condition.Reference#getNonReferenceScope()
	 * @see ompca.condition.Reference#getScope()
	 */
	@Override
	protected ConditionElement cacheScope() {
		final PathVariablePlaceholder pre = previous();
		if (pre == null) return getFunctionScope();
		
		if (enters(METHOD_CACHE_SCOPE)) return null;
		enter(METHOD_CACHE_SCOPE);
		ConditionElement scope = pre.getScope();
//		ConditionElement scope = debugCallDepth(()-> pre.getScope());
		if (scope == null) try {
			/* Parsing assignments returns variables/pointers directly
			 * and side-effects are better for scopes?
			 */
			scope = Proposition.fromRecursively(asn.getFirstClause(), cacheRuntimeAddress(), getCondGen());

		} catch (Exception e) {
			throwTodoException(e);
		}
		leave(METHOD_CACHE_SCOPE);
		return scope;
	}

	protected ompca.vodcg.condition.Function cacheFunctionScope() {
		return ompca.vodcg.condition.Function.getFunctionScopeOf(
				asn.getTopNode(), cacheRuntimeAddress(), asn.getCondGen());
	}

	
	
	@SuppressWarnings("unchecked")
	@Override
	protected <T> Set<? extends T> cacheDirectVariableReferences(
			Class<T> refType) {
		return guard(
				()-> (Set<T>) super.cacheDirectVariableReferences(refType),
				// reentering empty for continuing the initial entering without duplicates
				()-> Collections.emptySet());
//				()-> throwUncertainPlaceholderException("reentering caching", getAssignable()));
	}
	

	
	@Override
	protected void cacheDirectSideEffect() {
		if (tests(isAssigned())) super.cacheDirectSideEffect();
		else for (PathVariablePlaceholder asd : getAssigneds()) try {
			orSideEffect(asd.getAssignable().getConditions(null));
			
//		} catch (UncertainPlaceholderException e) {
//			throw e;
		} catch (Exception e) {
			throwTodoException(e);
		}
	}
	
	
	
	@Override
	public IASTFileLocation getFileLocation() {
		return getAssignable().getFileLocation();
	}
	
	public String getShortNameAddress() {
		return getAssignable().getShortNameAddress();
	}
	
	
	
	@Override
	public Assignable<?> getAssignable() {
		assert asn != null;
		return asn;
//		return (getSubject() == null) ? null : getSubject().getLValue();
	}
	
	@Override
	public Expression getAssignerIf() {
		return getAssignable().getAssigner();
//		return get(()-> peekVersion().getAssignerIf(),
//				()-> getAssignable().getAssigner());
	}

	/**
	 * @return empty set if this placeholder stores an uninitialized local parameter, which may have multiple (ambiguous)
	 * 	calling arguments.
	 * @see #previousRuntimeAssigneds()
	 */
	public Set<PathVariablePlaceholder> getAssigneds() {
		try {
			return tests(isAssigned()) 
					? Collections.singleton(this)
					: previousRuntimeAssigneds();
			
		} catch (Exception e) {
			return throwTodoException(e);
		}
	}

	@Override
	public void setAssigner(Expression rhs) {
		if (testsNot(isAssigned())) SystemElement.throwTodoException("inconsistent assignedness");
		super.setAssigner(rhs);
	}
	
//	/**
//	 * @return null if this placeholder stores an uninitialized local parameter, which may have multiple (ambiguous)
//	 * 	calling arguments.
//	 * @see #previous()
//	 */
//	@Override
//	public NavigableSet<PathVariablePlaceholder> previousRuntimeAssigneds() {
////		final PathVariablePlaceholder pre = previous();
////		return pre == null || tests(pre.isAssigned()) ? 
////				pre : pre.previousAssigned();
//	}

	/**
	 * @return the AST previous placeholder; 
	 * 	null if this placeholder stores a local parameter, 
	 * 	which may have multiple (ambiguous) calling arguments.
	 * @see Assignable#previous()
	 */
	@SuppressWarnings("unchecked")
	@Override
	public PathVariablePlaceholder previous() {
//			throws UncertainPlaceholderException {
		try {
			return applySkipNullThrow( 
					pAsn-> from(pAsn),
					()-> getAssignable().previous());
			
		} catch (Exception e) {
			return throwTodoException(e);
		}
	}
	
	/**
	 * @return the runtime previous placeholder; 
	 * 	null if this placeholder stores a local parameter, 
	 * 	which may have multiple (ambiguous) calling arguments.
	 * @see Assignable#previousRuntimes()
	 */
	@SuppressWarnings("unchecked")
	@Override
	public NavigableSet<PathVariablePlaceholder> previousRuntimes() {
//			throws UncertainPlaceholderException {
		try {
			final NavigableSet<PathVariablePlaceholder> pras = new TreeSet<>(this);
			for (Assignable<?> pra : getAssignable().previousRuntimes())
				pras.add(pra.getPathVariablePlaceholder());
			return pras;
			
		} catch (Exception e) {
			return throwTodoException(e);
		}
	}
	
	/**
	 * @return constant assigner or assigned l-value to keep acting as a placeholder 
	 * 	within an assignment {@link Equality}.
	 * @see ompca.vodcg.SystemElement#toConstantIf()
	 */
	@Override
	protected Expression toConstantIf() 
		throws ASTException, UncertainException {
		assert getAssigneds().size() == 1;
		return tests(isAssigned()) 
				? this 
				: getSkipNull(()->
				getAssigneds().iterator().next().getAssignerIf().toConstant()); 
//				: get(()-> previous().toConstantIf(),
//						e-> throwTodoException("constant should NOT be null", e));
	}

	/**
	 * L-value equivalence.
	 * 
	 * @see java.util.Comparator#compare(java.lang.Object, java.lang.Object)
	 */
	@Override
	public int compare(PathVariablePlaceholder vvd1, PathVariablePlaceholder vvd2) {
		if (vvd1 == vvd2) return 0;
		if (vvd1 == null || vvd2 == null) throwTodoException(
				"Incomparable delegates: " + 
					(vvd1 == null ? "'null'" : vvd1) + " and " + 
					(vvd2 == null ? "'null'" : vvd2));
		return vvd1.compareTo(vvd2);
	}

	/**
	 * L-value equivalence.
	 * 
	 * @see java.lang.Comparable#compareTo(java.lang.Object)
	 */
	@Override
	public int compareTo(PathVariablePlaceholder vvd2) {
		if (vvd2 == null) 
			throwNullArgumentException("Incomparable delegates: 'null' and " + vvd2 + "!");
		
		return getAssignable().compareTo(vvd2.getAssignable());
	}

	@Override
	protected boolean equalsToCache(SystemElement e2) {
		final PathVariablePlaceholder pvp2 = (PathVariablePlaceholder) e2;
		if (getAssignable().equals(pvp2.getAssignable())) return true;
		else if (tests(isAssigned()) && tests(pvp2.isAssigned())) return false;
		return super.equalsToCache(e2);
	}

	@Override
	protected List<Integer> hashCodeVars() {
		return Arrays.asList(getAssignable().hashCode());
	}

	
	
	public boolean isArray() {
		return getAssignable().isArray();
	}
	
	@Override
	public boolean isInAST() {
		return true;
	}

	@Override
	public boolean isPrivate() {
		return isThreadPrivate();
	}
	
	@Override
	public boolean isThreadPrivate() {
		return isArray() 
				? getAssignable().isThreadPrivate() 
				: super.isThreadPrivate();
	}
	
//	@Override
//	public Boolean dependsOn(Expression e) {
//		if (e instanceof PathVariablePlaceholder) 
//			if (tests(dependsOn((PathVariablePlaceholder) e))) return true;
//		return super.dependsOn(e); 
//	}
//	
//	protected boolean dependsOn(PathVariablePlaceholder pvp) {
//		for (VariablePlaceholder<?> dvp : getAssignable()) 
//			// ((VariablePlaceholder<?>) dvp).dependsOn(v) is already called at VariablePlaceholder
//			if (dvp != this && tests(dvp.dependsOn(pvp))) return true;
//		return false;
//	}

	@Override
	public boolean reversions() {
		return getAssignable().reversions();
	}
	
	/**
	 * ArrayAccessVersion.reversion(current_version)
	 * 
	 * @param args
	 * @throws NoSuchVersionException
	 */
	@SuppressWarnings("unchecked")
	final public void reversion(List<ArithmeticExpression> args) 
			throws NoSuchVersionException {
		if (args == null) throwNullArgumentException("arguments");
		
		ArrayAccessVersion<PathVariable> aav = null;
		final Assignable<?> asn = getAssignable();
//		final IASTArraySubscriptExpression array = asn.getEnclosingArraySubscriptExpression();
//		final FunctionalPathVariable fpv = array == null
//				? FunctionalPathVariable.from((IASTArrayDeclarator) asn.getDeclarator(), asn, asn.getPathVariable())
//				: FunctionalPathVariable.fromRecursively(array, ()-> getCondGen());
		try {
			final Version<? extends PathVariable> cv = peekVersion();
			if (cv instanceof ArrayAccessVersion) {
				final ArrayAccessVersion<PathVariable> cav = (ArrayAccessVersion<PathVariable>) cv;
				if (!cav.getArguments().equals(args)) cav.setArguments(args);
				return;
			}
			
			aav = (ArrayAccessVersion<PathVariable>) ArrayAccessVersion.from(args, null, asn, cv.getThreadRole());
			aav.subversion((Version<? extends FunctionalPathVariable>) cv);
			
		} catch (NullPointerException e) {	// cv == null 
		} catch (ReenterException | UncertainPlaceholderException e) {
			// thrown by recursive version initialization
			e.leave();
			
		} catch (Exception e) {
//		} catch (ClassCastException | NoSuchVersionException e) {
			throwTodoException(e);
			
		} finally {
			setVersion(aav == null
					? ArrayAccessVersion.from(args, null, asn, asn.initRole())
					: aav);
		}
	}
	
	/**
	 * Updating the top placeholder access version on demand 
	 * and outside the array/pointer constructions.
	 * 
	 * @param reversioning
	 * @param conditions
	 */
	@SafeVarargs
	final public void reversion(Runnable reversioning, Supplier<Boolean>...conditions) {
		this.reversioning = reversioning;
		this.reversionConditions = conditions;
	}
	
	/**
	 * @param role - the role for non-AST version, which may be AST-underivable
	 * @return some version instead of this shared placeholder 
	 * 	for explicitly version-ing cloned expressions.
	 */
	@SuppressWarnings("unchecked")
	@Override
	public <T extends ConditionElement> T cloneReversion(
			final IASTStatement blockStat, FunctionallableRole role, Version<? extends PathVariable> ver) {
		return isShared() || (role != null && role.isShared())
				? (T) this
				: debugGet(()-> super.cloneReversion(blockStat, role, ver));
//				determineASTVersion(getAssignable(), blockStat, null, ver)	// the role may be AST-underivable 
//				.cloneIfChangeRole(role));
		
//		try {
//			final Assignable<?> asn = getAssignable();
//			// array role should not be changed 
////			role = asn.isThreadPrivate() ? role : asn.initRole();
//			reversion(determineVersion(asn, blockStat, role, ver));
//			ver = getVersion(role);
//			ver.setNonAST();
//			return (T) ver;
//			
//		} catch (UncertainPlaceholderException e) {	// thrown by determineVersion(...)
//			if (ver == null) throwTodoException(e);
//			setVersion(ver);
//			return (T) ver;
//		} catch (Exception e) {
//			return throwUnhandledException(e);
//		}
	}


	
//	/**
//	 * Assigner-replaceable if constant
//	 */
//	@Override
//	public ArithmeticExpression add(ArithmeticExpression addend) throws ASTException {
//		return tests(isConstant()) 
//				? ((ArithmeticExpression) toConstantIf()).add(addend)
//				: super.add(addend);
//	}
//
//	/**
//	 * Assigner-replaceable if constant
//	 */
//	@Override
//	public ArithmeticExpression subtract(ArithmeticExpression subtrahend) throws ASTException {
//		return tests(isConstant()) 
//				? ((ArithmeticExpression) toConstantIf()).subtract(subtrahend)
//				: super.subtract(subtrahend);
//	}
//	
//	/**
//	 * Assigner-replaceable if constant
//	 */
//	@Override
//	public ArithmeticExpression multiply(ArithmeticExpression multiplicand) throws ASTException {
//		return tests(isConstant()) 
//				? ((ArithmeticExpression) toConstantIf()).multiply(multiplicand)
//				: super.multiply(multiplicand);
//	}
//	
//	/**
//	 * Assigner-replaceable if constant
//	 */
//	@Override
//	public ArithmeticExpression divide(ArithmeticExpression divisor) throws ASTException {
//		return tests(isConstant()) 
//				? ((ArithmeticExpression) toConstantIf()).divide(divisor)
//				: super.divide(divisor);
//	}
	

	
	@Override
	public Expression negate() throws ASTException {
		if (getAssigneds().size() > 1) throwTodoException("conditional negation disjunction");
		for (PathVariablePlaceholder asd : getAssigneds()) {
			final Expression asnr = getSkipNull(()->
			asd.getAssignerIf());
			return asnr == this || asnr == null
					? super.negate()
					: asnr.negate();
		}
		return null;
	}
	
	
	
//	/**
//	 * @param newDelegate
//	 */
//	public void replaceBy(PathVariableDelegate newDelegate) {
//		if (newDelegate == null) Debug.throwInvalidityException("null new delegate");
//		
//		ThreadRole newRole = newDelegate.getThreadRole();
//		if (!getVersion().matches(newRole)) 
//			Debug.throwTodoException("un-matching version and role");
//		AST_PV_PLACEHOLDERS.put(assignable, newRole, newDelegate);
//	}
	

	
//	@Override
//	public Proposition toProposition() {
//		return guardReenter(
//				()-> getAssignable().getPathCondition().getAssertion(),
//				()-> throwUncertainPlaceholderException(METHOD_TO_PROPOSITION),
//				METHOD_TO_PROPOSITION);
//	}


	
	@Override
	public String toNonEmptyString(boolean usesParenthesesAlready) {
//		if (Elemental.tests(isConstant())) 
//			return ((PathVariableDelegate) toConstantIf()).getAssigner().toNonEmptyString(usesParenthesesAlready);
		final String sna = "?" + getAssignable().getShortNameAddress();
		return super.isEmpty() 
				? sna
				: guard(
						()-> super.toNonEmptyString(usesParenthesesAlready), 
						()-> sna + " @ recursion",
						e-> sna + " @ " + e,
						METHOD_TO_NON_EMPTY_STRING);
	}

//	@Override
//	public String toZ3SmtString(boolean printsVariableDeclaration, 
//			boolean printsFunctionDefinition) {
////		if (isConstant()) return lastAssigner().toZ3SmtString(
////				printsVariableDeclaration, printsFunctionDefinition);
//		return super.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition);
//	}

	
	
	public <T> T throwUncertainPlaceholderException(Method callee) 
			throws UncertainPlaceholderException {
		return getAssignable().throwUncertainPlaceholderException(callee);
	}
	
}