package ompca.vodcg.condition;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.NavigableSet;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;

import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.Addressable;
import ompca.MappableList;
import ompca.vodcg.Assignable;
import ompca.vodcg.IncomparableException;
import ompca.vodcg.ReenterException;
import ompca.vodcg.SystemElement;
import ompca.vodcg.UncertainPlaceholderException;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.data.ArithmeticGuard;
import ompca.vodcg.condition.data.ArrayType;
import ompca.vodcg.condition.data.PlatformType;
import ompca.vodcg.condition.data.PointerType;
import ompca.vodcg.condition.version.FunctionalVersion;
import ompca.vodcg.condition.version.FunctionallableRole;
import ompca.vodcg.condition.version.MutexAssignedVersion;
import ompca.vodcg.condition.version.NoSuchVersionException;
import ompca.vodcg.condition.version.ThreadPrivateVersion;
import ompca.vodcg.condition.version.ThreadRole;
import ompca.vodcg.condition.version.ThreadRoleMatchable;
import ompca.vodcg.condition.version.UniversalVersion;
import ompca.vodcg.condition.version.Version;
import ompca.vodcg.condition.version.VersionEnumerable;
import ompca.vodcg.condition.version.VersionPlaceholder;

/**
 * TODO: The scope of a variable placeholder is limited to the scope of subject version,
 * which is different from the variable's declaration.
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class VariablePlaceholder<V extends Variable> 
extends VersionPlaceholder<V> {

	/**
	 * For non-AST one-one mapped variables (and their placeholder's).
	 * It uses linear map access since the hash map access depends on some enumerator of Version
	 * and the construction of enumerator (VariablePlaceholder) depends on the Version back and forth.
	 */
	private static final Map<Version<? extends Variable>, VariablePlaceholder<? extends Variable>> 
	VAR_PLACEHOLDERS 	= new MappableList<>();
//	VAR_PLACEHOLDERS 	= new HashMap<>();
	
//	private static final Method METHOD_GET_DIRECT_VARIABLE_REFERENCES = Elemental.getMethod(
//			VariablePlaceholder.class, "getDirectVariableReferences");
//	private static final Method 
//	METHOD_SET_VERSION = Elemental.getMethod(VariableDelegate.class, "setVersion", Version.class);

	/**
	 * Side effect of this placeholder varies by {@link #versions} 
	 * except data type constraints.
	 */
	private Map<FunctionallableRole, Version<? extends V>> versions = null;
//	private EnumMap<ThreadRole, Version<? extends V>> versions;
//	final private List<Version<? extends V>> 
//	tpfVersions 	= new ArrayList<>();

	
	
	/**
	 * @param ver - default version
	 * @throws NoSuchVersionException 
	 */
	protected VariablePlaceholder(Version<? extends V> ver, boolean isInAST, Boolean isGlobal, Boolean isAssigned, Expression rhs) {
		super(ver, isInAST, isGlobal, isAssigned, rhs);	// holding default version in the only operand
		VAR_PLACEHOLDERS.put(ver, this);
	}

	protected VariablePlaceholder(String name, Function<Reference<Version<? extends V>>, Version<? extends V>> verSup, 
			boolean isInAST, Boolean isGlobal, VODCondGen condGen) {
		this(name, verSup, isInAST, isGlobal, null, null, condGen);
	}
	
	protected VariablePlaceholder(String name, Function<Reference<Version<? extends V>>, Version<? extends V>> verSup, 
			boolean isInAST, Boolean isGlobal, Boolean isAssigned, Expression rhs, VODCondGen condGen) {
		super(name, verSup, isInAST, isGlobal, isAssigned, rhs, condGen);
	}



	@SuppressWarnings("unchecked")
	@Override
	public <T extends ConditionElement> T cloneIfChangeRole(final FunctionallableRole role) {
		if (peekVersion(role) != null) return (T) this;
		
		final Version<? extends V> ver = peekVersion();
		if (ver == null) throwNullArgumentException("version");
		
		final Expression asner = ver.getAssigner();
		return (T) new VariablePlaceholder<>(getName(), 
				addr -> (Version<? extends V>) ver.cloneIfChangeRole(role), 
				isInAST(), 
				isGlobal(),
				ver.isAssigned(),
				getSkipNull(()-> asner == this ? asner : asner.cloneIfChangeRole(role)),
				getCondGen()); 
//		return (T) fromNonAST((Version<? extends V>) ver.cloneIfChangeRole(role), isGlobal()); 
	}

	@SuppressWarnings("unchecked")
	@Override
	public <T extends ConditionElement> T cloneReversion(
			IASTStatement blockStat, final FunctionallableRole role, Version<? extends PathVariable> ver) {
		try {
//			final T sc = debugGet(null, ()-> super.cloneReversion(blockStat, role, ver), blockStat, role, ver);
			final T sc = super.cloneReversion(blockStat, role, ver);
			if (sc == this) return (T) this;
			
		} catch (NoSuchVersionException e) {
		}
		
		// from non-AST placeholder's to AST ones
		assert role != null;
		if (role.isShared()) {
			final Assignable<?> asn = getAssignable();
			if (asn != null) return asn.getPathVariablePlaceholder().cloneReversion(blockStat, role, ver);
		}

		// getThreadRole() != role
		if (ver == null) ver = (Version<? extends PathVariable>) getVersion(role);	// getVersion(role) returns no clones
		if (ver == null) ver = (Version<? extends PathVariable>) peekVersion();
		ver = (Version<? extends PathVariable>) ver.cloneIfChangeRole(role); 
		final Version<? extends PathVariable> ver_ = ver; 
		final VariablePlaceholder<? extends Variable> vp = fromNonAST(ver_);
		return (T) (vp != this
				? vp
				: new VariablePlaceholder<>(ver_, ver_.isInAST(), ver_.isGlobal(), vp.isAssigned(), vp.getAssigner()));
	}

	
	
	/**
	 * @param vars1
	 * @param vars2
	 * @return {@code vars1} - {@code vars2} and non-null.
	 */
	public static Set<VariablePlaceholder<?>> differVariables(
			@SuppressWarnings("rawtypes") 
			Set<? extends VariablePlaceholder> vars1, 
			Set<VariablePlaceholder<?>> vars2) {
		if (vars1 == null) return Collections.emptySet();
		
		final Set<VariablePlaceholder<?>> dvs = new HashSet<>();
		for (VariablePlaceholder<?> v1 : vars1) try {
			dvs.add((VariablePlaceholder<?>) v1);
		} catch (ClassCastException e) {
			throwTodoException(e);
		}
		
		for (VariablePlaceholder<?> v2 : vars2) {
			List<VariablePlaceholder<?>> eqVrs = new ArrayList<>();
			for (VariablePlaceholder<?> v1 : dvs) 
				if (tests(v1.equals(v2))) eqVrs.add(v1);
			dvs.removeAll(eqVrs);
		}
		return dvs;
	}
	
	
	
	public static VariablePlaceholder<? extends Variable> fromNonAST(Variable v, Boolean isGlobal) {
		if (v == null) throwNullArgumentException("variable");
		try {
			for (VariablePlaceholder<? extends Variable> navp : VAR_PLACEHOLDERS.values())
				if (navp.getVariable() == v) return navp;
			return fromNonAST(new UniversalVersion<Variable>(v, isGlobal), isGlobal);	// universal versions may be used in local constants
			
		} catch (NoSuchVersionException e) {
			return throwUnhandledException(e);
		}
	}

//	public static VariablePlaceholder<? extends Variable> fromNonAST(
//			Variable v, ThreadRole role, Boolean isGlobal, Function<Reference<Version<? extends Variable>>, Version<? extends Variable>> verSup) {
//		VariablePlaceholder<? extends Variable> vp = fromNonAST(v, isGlobal);
//		if (!vp.getThreadRole().equals(role)) vp = fromNonAST(v.getName(), isGlobal, v.getCondGen(), verSup);
//		return vp;
//	}
	
	public static VariablePlaceholder<? extends Variable> fromNonAST(Version<? extends Variable> version) {
		if (version == null) throwNullArgumentException("version");

		return fromNonAST(version, version.isGlobal());
	}
	
	/**
	 * This method is ONLY for generating a non-AST variable placeholder!
	 * 
	 * @param version - source version, maybe in AST
	 * @return
	 * @throws NoSuchVersionException
	 */
	public static VariablePlaceholder<? extends Variable> fromNonAST(Version<? extends Variable> version, Boolean isGlobal) {
		return matchOrNew(version, false, isGlobal);
	}
	
	/**
	 * @param name - should be role independent
	 * @param isGlobal
	 * @param condGen
	 * @param verSup
	 * @return
	 */
	public static VariablePlaceholder<? extends Variable> fromNonAST(
			String name, Boolean isGlobal, Boolean isAssigned, Expression rhs, VODCondGen condGen, 
			Function<Reference<Version<? extends Variable>>, Version<? extends Variable>> verSup) {
		if (name == null) throwNullArgumentException("name");
		if (verSup == null) throwNullArgumentException("version supplier");
		
		for (VariablePlaceholder<? extends Variable> vp : VAR_PLACEHOLDERS.values())
			if (vp.getName().equals(name)) return vp;

		return new VariablePlaceholder<>(name, verSup, false, isGlobal, isAssigned, rhs, condGen);
	}
	
	/**
	 * @param name - should be role independent
	 * @param type
	 * @param isParameter
	 * @param isGlobal
	 * @param funcScope
	 * @param astScope
	 * @param condGen
	 * @return
	 */
	public static VariablePlaceholder<? extends Variable> fromNonAST(String name, 
			PlatformType type, boolean isParameter, Boolean isGlobal, 
			Supplier<ompca.vodcg.condition.Function> funcScope, IASTStatement astScope, VODCondGen condGen) {
		return fromNonAST(Variable.fromNonAST(
				name, type, isParameter, funcScope, astScope, condGen),
				name, type, isParameter, isGlobal, funcScope, astScope, condGen);
	}
	
	/**
	 * @param v
	 * @param name - should be role independent
	 * @param type
	 * @param isParameter
	 * @param isGlobal
	 * @param funcScope
	 * @param astScope
	 * @param condGen
	 * @return
	 */
	private static VariablePlaceholder<? extends Variable> fromNonAST(Variable v, String name, 
			PlatformType type, boolean isParameter, Boolean isGlobal, 
			Supplier<ompca.vodcg.condition.Function> funcScope, IASTStatement astScope, VODCondGen condGen) {
		final VariablePlaceholder<? extends Variable> vp = fromNonAST(v, getSkipNull(()-> !isParameter && isGlobal));
		
		// assumed assigned if in non-primitive-varargs pointer type
		setA: if (type instanceof PointerType) {
			if (type instanceof ArrayType) {
				final ArrayType at = (ArrayType) type;
				if (at.isVarargs()) {
					vp.setAssigned(!at.getType().isPrimitive());
					break setA;
				}
			}
			vp.setAssigned(true);
		}
		return vp;
	}

	@SuppressWarnings("unchecked")
	static public VariablePlaceholder<? extends Variable> fromSelfAssigning(PathVariablePlaceholder assigned) 
			throws NoSuchVersionException {
		if (assigned == null) throwNullArgumentException("assigned");
		
		final VODCondGen cg = assigned.getCondGen();
		final Assignable<?> asd = assigned.getAssignable();
		final Function<Reference<Version<? extends Variable>>, Version<? extends Variable>> fv = addr-> (Version<FunctionalPathVariable>) 
				FunctionalVersion.from((VersionEnumerable<FunctionalPathVariable>) addr, asd.getFunctionalArguments(), asd.getDependentLoops(), cg);
		return (VariablePlaceholder<FunctionalPathVariable>) fromNonAST(
				assigned.getShortNameAddress() + "_2", assigned.isGlobal(), false, null, cg, fv);
	}
	
	
	
	/**
	 * @param v
	 * @param blockStat
	 * @param role - {@link ThreadRole#FUNCTION} means to return a non-loop-iterator functional argument
	 * @param isGlobal
	 * @return a separated thread-private placeholder for the given <code>role</code>
	 */
	public static VariablePlaceholder<? extends Variable> getThreadPrivate(
			Variable v, IASTStatement blockStat, ThreadRole role, Boolean isGlobal, Boolean isAssigned, Expression rhs) {
		try {
			VariablePlaceholder<? extends Variable> vp = fromNonAST(v, isGlobal);
			if (!vp.getThreadRole().equals(role)) {
//				final VariablePlaceholder<? extends Variable> vp_ = vp;
				vp = new VariablePlaceholder<>(
						v.getName(),
						addr-> ThreadPrivateVersion.from((VariablePlaceholder<Variable>) addr, v, blockStat, role),
						v.isInAST(),
						isGlobal,
						isAssigned,
						rhs,
//						getSkipNull(()-> vp_.getAssigner().cloneIfChangeRole(role)),
						v.getCondGen());
				vp.setType(v.getType());
			}
			return vp;
			
		} catch (IllegalArgumentException | NoSuchVersionException e) {
			return throwUnhandledException(e);
		}
	}
	
	private static VariablePlaceholder<? extends Variable> matchOrNew(
			Version<? extends Variable> version, boolean isInAST, Boolean isGlobal) {
		if (version == null) throwNullArgumentException("version");
		
		VariablePlaceholder<? extends Variable> vp = VAR_PLACEHOLDERS.get(version);
		if (vp == null) {
			// with side-effect of VAR_PLACEHOLDERS.put(version, vp);
			vp = new VariablePlaceholder<>(
					version, isInAST, isGlobal, version.isAssigned(), version.getAssigner());
		}
		return vp;
	}
	
	

	@Override
	public boolean matches(Version<? extends V> newVer) {
		// super.matches(newVer) without role-matching
		return super.matches(newVer) && getMatchedRole(newVer) != null;
	}
	
	public ThreadRole getMatchedRole(Version<? extends V> newVer) {
		if (newVer == null) throwNullArgumentException("new version");
		
		final ThreadRoleMatchable nrm = newVer.getThreadRole();
		if (nrm == null) throwNullArgumentException("thread role");
//		if (!newVer.matches(nrm)) 
//			Version.throwNoSuchVersionException(nrm);
		
		ThreadRole nr = null;
		if (nrm instanceof ThreadRole) 
			nr = (ThreadRole) nrm;
		else if (nrm instanceof FunctionallableRole) 
			nr = ((FunctionallableRole) nrm).getBasic();
		if (nr == null) throwTodoException("unsupported role");
		return nr;
	}
	
	
	
	@Override
	public Version<? extends V> peekVersion(ThreadRoleMatchable role) {
		if (role == null) return super.peekVersion(role);
		
		final Map<FunctionallableRole, Version<? extends V>> vs = peekVersionMap();
		if (vs != null) {	// after field versions' initialized
//			if (role instanceof ThreadRole) 
//				return vs.get(role);
			if (role instanceof FunctionallableRole) 
				return vs.get((FunctionallableRole) role);
			throwUnsupportedRoleException();
		}
		return null;
	}
	
	/**
	 * @return the current version referenced
	 */
	@Override
	public Version<? extends V> getVersion() {
		return debugGet(()-> ((SystemElement) this).guard(
				()-> getVersion(getThreadRole()),
				()-> super.getVersion()));
	}

	/**
	 * @return the current version referenced
	 */
	@Override
	public Version<? extends V> getVersion(FunctionallableRole role) {
		if (role == null) return super.getVersion();

		Version<? extends V> ver = null;
		final Map<FunctionallableRole, Version<? extends V>> map = getVersionMap();
		if (map.isEmpty()) {	// peekVersion() == null
			ver = super.getVersion().cloneIfChangeRole(role);
			
		} else if (role instanceof FunctionallableRole) try {
			ver = map.get((FunctionallableRole) role);
			if (ver == null) ver = super.getVersion().cloneIfChangeRole(role);
			
		} catch (Exception e) {
			return throwTodoException(e);
		} else 
			// unsupported thread role
			throwUnsupportedRoleException();
//		if (role.isFunctional()) return versions.get(br).get(role.getArguments());
		
		if (ver != null) {
			setVersion(ver);
//			if (ver.getThreadRole().equals(role)) return ver;
		}
		return ver;
	}
	
	@SuppressWarnings("unchecked")
//	public <T extends Version<? extends V>> T getVersion(Class<T> type) {
	public <T> T getVersion(Class<T> type) {
		if (type == null) throwNullArgumentException("version type");
		
		final Collection<Version<? extends V>> vers = getVersions();
		for (Version<? extends V> ver : vers) 
			if (type.isInstance(ver)) return (T) ver;
		for (Version<? extends V> ver : vers) {
			final T sub = ((Version<V>) ver).getSubversion(type);
			if (sub != null) return sub;
		}
		return null;
	}
	
	/**
	 * @return @NotNull
	 */
	public Collection<Version<? extends V>> getVersions() {
		try {
			final Collection<Version<? extends V>> vs = getVersionMap().values();
			if (!vs.isEmpty()) return vs;
			
		} catch (UncertainPlaceholderException e) {	// thrown by getVersionMap()
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
		return Collections.singletonList(getVersion());
	}
	
	/**
	 * @return @NotNull
	 */
	public Collection<Version<? extends V>> peekVersions() {
		return peekVersionMap().values();
	}
	
	/**
	 * @return @NotNull
	 * @throws ReenterException
	 * @throws IncomparableException
	 * @throws UncertainPlaceholderException
	 */
	private Map<FunctionallableRole, Version<? extends V>> getVersionMap() 
			throws ReenterException, IncomparableException, UncertainPlaceholderException {
		final Map<FunctionallableRole, Version<? extends V>> vs = peekVersionMap();
//		if (vs.isEmpty()) getVersion();
		return vs;
	}
	
	/**
	 * @return @NotNull
	 */
	private Map<FunctionallableRole, Version<? extends V>> peekVersionMap() {
		// versions may be uninitialized when used by setVersion(...) during superclass's setVersion(...)
//		if (versions == null) versions = new EnumMap<>(ThreadRole.class);
		if (versions == null) versions = new HashMap<>();
		return versions;
	}
	
	/**
	 * This method does role-changing reversion 
	 * while it doesn't do subversion-ing.
	 */
	@Override
	public void setVersion(Version<? extends V> newVer) {
		final ThreadRole nr = getMatchedRole(newVer);
		if (nr == null) throwTodoException("unmatching version");

//		final ThreadRoleMatchable cr = peekThreadRole();
//		if (cr == null || cr.derives(nr)) {
//			final Version<? extends V> cvPre = peekVersion();
//			if (cvPre == peekVersion()) return;
//		} 
		
		// for both derivable and underivable versions
		final Version<? extends V> cv = peekVersion();
		if (cv == null || cv.derives((ThreadRoleMatchable) newVer)) 
			super.setVersion(newVer);
		peekVersionMap().put(nr, newVer);
		
		// AST ones are stored in PathVariablePlaceholder.AST_PV_PLACEHOLDERS
		if (!isInAST()) VAR_PLACEHOLDERS.put(newVer, this);
		
		final Version<? extends V> cvPost = peekVersion();
		final Map<FunctionallableRole, Version<? extends V>> vmapPost = peekVersionMap();
		if ((cvPost != null && vmapPost.isEmpty()) || (cvPost == null && !vmapPost.isEmpty()))
			throwTodoException("inconsistent version map");
		
//		if (enters(METHOD_SET_VERSION))	// bypassing reentered/recursive version initialization 
//			super.setVersion(nv);		// assert cv == null
//		else {
//			enter(METHOD_SET_VERSION);
//			final Version<V> cv = (Version<V>) getVersion(nr);
//			if (cv == newVersion) return;
//			
//			// conditionally initiating version or subversion-ing
//			if (cv == null || (nxr == null ? cv.matches(nr) : cv.matches(nxr))) super.setVersion(nv);
//			else {
//				cv.changeRole(nr).subversion(nv);
//				nv = cv;
//			}
//			leave(METHOD_SET_VERSION);
//		}
	}
	
	
	
	@Override
	public void setFunctionScope(Supplier<ompca.vodcg.condition.Function> scope) {
		if (isParameter()) {
			if (scope == null) throwInvalidityException("non-global parameter");

			assert getVariable() != null;
			getVariable().setFunctionScope(scope);
			for (Version<? extends V> ver : getVersions())
				ver.setFunctionScope(scope);
		}
		super.setFunctionScope(scope);
	}
	
	
	
	@Override
	public void setAssigner(Expression rhs) {
		try {
			super.setAssigner(rhs);
			if (rhs == null) return;

			final FunctionallableRole rhsRole = rhs.getThreadRole();
			final Version<? extends V> ver = peekVersion(rhsRole);
			if (ver != null) ver.setAssigner(rhs);
			else if (tests(rhsRole.isConstant())) {
				for (Version<? extends V> v : getVersions())
					v.setAssigner(rhs);
//				else throwTodoException("conditional constant assigners");
			} 
		} catch (UncertainPlaceholderException e) {
			// version is not ready during recursive placeholder initialization
			e.leave();
			
		} catch (Exception e) {
			throwUnhandledException(e);
		}
	}
	
	
	
//	@Override
//	public String getShortAddress() {
//		return get(()-> super.getShortAddress(),
//				()-> getName());
//	}
	
	
	
	public V getVariable() {
		return getSubject().getSubject();
	}
	
	/**
	 * @return Given <code>refType</code> asking for {@link Version}, 
	 * 	a non-null {@link Set} wrapper of <em>the current in-use version only</em> 
	 * 	is returned while other versions are left as indirect reference sources since they may be 
	 * 	mutual-exclusive like ones in {@link MutexAssignedVersion}'s and not suitable 
	 * 	for mutex-free uses.
	 * @see ompca.conditionence#getDirectVariableReferences()
	 */
	@SuppressWarnings("unchecked")
	@Override
	protected <T> Set<? extends T> cacheDirectVariableReferences(
			Class<T> refType) {
		if (refType == null) return throwNullArgumentException(
				"reference type", ()-> Collections.emptySet());
		
		final Set<T> dvrs = new HashSet<>(
				super.cacheDirectVariableReferences(refType));
		try {
			// caching ALL versions
			if (refType.equals(Version.class)) 
				dvrs.addAll((Collection<T>) getVersions());
			// caching specific version
			else if (refType.asSubclass(Version.class) != null) 
				dvrs.add(getVersion(refType));
			
		} catch (ClassCastException e) {	// refType == VariablePlaceholder, PathVariablePlaceholder...
		}
		// condition placeholder versions are mutual-exclusive hence NOT necessary to include
//		if (!enters(METHOD_GET_DIRECT_VARIABLE_REFERENCES)) {	
//			enter(METHOD_GET_DIRECT_VARIABLE_REFERENCES);
//			for (Version<? extends V> ver : getVersions()) 
//				vrs.addAll(ver.getDirectVariableReferences());
//			leave(METHOD_GET_DIRECT_VARIABLE_REFERENCES);
//		}
		return dvrs; 
	}
	
	
	
	/**
	 * @return null since no arithmetic expression combination yet
	 */
	@Override
	protected Set<ArithmeticGuard> cacheArithmeticGuards() {
		return null;
	}
	
//	/**
//	 * Artificial variables are default to non-constants.
//	 */
//	@Override
//	protected Boolean cacheConstant() {
//		return false;
//	}
	
	
	
	@Override
	protected ConditionElement cacheScope() {
		ConditionElement scope = null;
		for (Version<? extends V> ver : getVersions())
			scope = getCommonScope(scope, ver.getScope());
		return scope != null 
				? scope 
				: super.cacheScope();
	}
	
	
	
	@Override
	public Boolean dependsOn(Expression e) {
		if (debugTests(()-> super.dependsOn(e))) return true;	// e == this
		
		Boolean vd = null;
		boolean vdNull = false;
		for (Version<? extends V> v : getVersions()) {
			vd = debugGet(()-> v.dependsOn(e));
			if (vd == null) {vdNull = true; continue;}
			if (vd) return true;
		}
		return vdNull ? null : vd;
	}

	@Override
	public boolean derives(Addressable address2) {
		return address2 instanceof VariablePlaceholder && super.derives(address2);
	}

	@Override
	public boolean derives(ThreadRoleMatchable matchable2) {
		boolean result = false;
		if (matchable2 instanceof Version) result = derives((Version<?>) matchable2);
		return result ? result : super.derives(matchable2);
	}
	
	protected boolean derives(Version<?> ver) {
		for (Version<? extends V> v : peekVersions())
			if (v == ver || v.derives((ThreadRoleMatchable) ver)) return true;
		return false;
	}
	
	@Override
	public boolean isParameter() {
		return getVariable().isParameter();
	}
	
//	/**
//	 * Faster checking for constant variables.
//	 * @see ompca.ompca.conditionxpression#isPositiveInfinity()
//	 */
//	@Override
//	public Boolean isPositiveInfinity() {
//		final Expression asgn = getAssigner();
//		// for non-self assigned's, oo++/-- == oo
//		if (asgn == this) return 
//				((NumericExpression) previousAssigner()).isPositiveInfinity();	
//		// for Boolean constants, etc.
//		else if (asgn instanceof NumericExpression) return 
//				((NumericExpression) asgn).isPositiveInfinity();	
////				debugCallDepth(()-> ((NumericExpression) asgn).isPositiveInfinity());	
//		
//		return super.isPositiveInfinity();
////		return guardSkipException(()-> 
////		super.isPositiveInfinity(), METHOD_IS_POSITIVE_INFINITY);
//	}
	
	
	
	public boolean isVarargs() {
		final PlatformType t = getType();
		return t instanceof ArrayType && ((ArrayType) t).isVarargs();
	}
	
	public boolean equalsVariable(VariablePlaceholder<?> vd2) {
		return equalsVariable(vd2.getVariable());
	}
	
	public boolean equalsVariable(Variable v) {
		return getVariable().equals(v);
	}
	
	/**
	 * Equality checking for merging placeholder's.
	 * @see ompca.conditompca.conditionaceholder#equalsToCache(ompca.vodcg.SystemElement)
	 */
	@Override
	protected boolean equalsToCache(SystemElement e2) {
		final VariablePlaceholder<?> vd2 = (VariablePlaceholder<?>) e2;
		try {
			// only primitive variables need numerical equality checking
			if (getType().isNumeric() && vd2.getType().isNumeric())
				if (!isLessThan(vd2) && !vd2.isLessThan(this)) return true;
			
		} catch (ReenterException e) {
			e.leave();
		} catch (NullPointerException e) {}
		return super.equalsToCache(e2);
	}
	
//	@Override
//	protected List<Integer> hashCodeVars() {
//		return isArithmeticType() && Elemental.tests(isConstant()) 
//				? Arrays.asList(toConstant().hashCode())
//				: super.hashCodeVars();
//	}
	
	
	
	@Override
	public Expression negate() {
		if (tests(isConstant())) {
			if (tests(isAssigned())) return getAssignerIf().negate();	// including constant self-assignment
			else {
				final Expression pasner = previousAssigner();
				if (pasner != null) return pasner.negate();
				throwTodoException("non-assigned constant");
			}
		} 
		return super.negate();
	}
	

	
	@SuppressWarnings("unchecked")
	@Override
	public <T extends Addressable> T previous() {
		final T sp = (T) super.previous();
		if (sp != null) return sp;
		
		if (!isDeclarator()) {
			final Assignable<?> asn = getAssignable(), ap = getSkipNull(()-> asn.previous());
			for (VariablePlaceholder<? extends Variable> vp2 : VAR_PLACEHOLDERS.values()) {
				if (vp2 == this) continue;
				if (equalsVariable(vp2)) {
					final Assignable<?> asn2 = vp2.getAssignable();
					if (asn == asn2 || tests(asn.isBefore(asn2))) continue;
					if (ap != null && ap == asn2) 
						return (T) vp2; 
					// mutually dependent non-AST placeholder's mean equal ordering
					if (debugGet(()-> vp2.guard(()-> vp2.previous() == null, ()-> false))) 
						return (T) vp2;
				}
			}
		}
		return null;
	}
	
	@Override
	public <T extends Addressable> NavigableSet<T> previousRuntimes() {
		return previous();
	}
	
	@Override
	public void reversion(Version<? extends V> newVer) {
		if (newVer == null) throwNullArgumentException("new version");
		
		super.reversion(newVer);
		
		if (!equalsVariable(newVer.getSubject())) 
			throwInvalidityException("inconsistent version subjects"); 
	}


	
//	private <T> T throwTodoException() {
//		return throwTodoException("Unsupported variable type!");
//	}
	
//	@Override
//	public String toNonEmptyString(boolean usesParenthesesAlready) {
//		return getID(null);
//	}
	
//	@Override
//	public String toZ3SmtString(boolean printsVariableDeclaration, 
//			boolean printsFunctionDefinition) {
//		final FunctionalVersion fv = getVersion(FunctionalVersion.class);
//		return fv == null
//				? super.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition)
//				: fv.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition);
//				
////		final String[] debug = {"a_4_randdp_c", "t2_60_randdp_c", "t1_56_randdp_c", "t1_47_randdp_c", "x_4_randdp_c"};
////		for (final String d : debug) if (str.contains(d) && !Version.findsDeclaration(str)) 
////			throwTodoException("non-declared variable");
//	}

}