/**
 * 
 */
package ompca.vodcg.condition.version;

import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.NavigableSet;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Supplier;

import org.eclipse.cdt.core.dom.IName;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.Elemental;
import ompca.condition.SerialFormat;
import ompca.solver.CarryInRangeDegrader;
import ompca.vodcg.ASTAddressable;
import ompca.vodcg.ASTException;
import ompca.vodcg.Assignable;
import ompca.vodcg.IncomparableException;
import ompca.vodcg.SystemElement;
import ompca.vodcg.UncertainPlaceholderException;
import ompca.vodcg.condition.AssignableExpression;
import ompca.vodcg.condition.ConditionElement;
import ompca.vodcg.condition.Expression;
import ompca.vodcg.condition.PathVariable;
import ompca.vodcg.condition.Reference;
import ompca.vodcg.condition.Referenceable;
import ompca.vodcg.condition.Variable;
import ompca.vodcg.condition.data.PlatformType;
import ompca.vodcg.condition.version.ThreadRole.ExtendedRole;

/**
 * Root class for versioning rewritable variables.
 * A value-changing means a version-changing.
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
abstract public class Version<Subject extends Referenceable> 
extends Reference<Subject> 
implements ASTAddressable, AppendableVersion<Subject>, AssignableExpression, ThreadRoleMatchable {

//	public enum Type {
//		Universal, ConstantCounting, Enumerated, ArrayAccess, Functional
//	}

//	private static final DuoKeyMap<VersionEnumerable<?>, ThreadRole, Version<?>> 
//	CACHE = new DuoKeyMap<>();
	/**
	 * Using Set is better than Map since a conditional assigned version may map to multiple declarations
	 */
//	private static final Set<String> 					DECL_CACHE = new HashSet<>();
	
	static private final Method METHOD_TO_Z3_SMT_STRING = 
			Elemental.getMethod(Version.class, "toZ3SmtString", boolean.class, boolean.class, boolean.class);

	
	
	/**
	 * Allowing, for example, PathVariable <em>super</em> 
	 * 	FunctionalPathVariable makes ArrayAccessVersion<FunctionalPathVariable> 
	 * 	reversion-able at all Assignable<PathVariable>'s.
	 */
	private VersionEnumerable<Subject> addr = null;
	private FunctionallableRole role;
	
	/**
	 * Serialization-based subversion-ing.
	 * 
	 * For example, UniversalVer_EnumeratedVer[FunctionalVer] 
	 * => EnumeratedVer.subversion(FunctionalVer)
	 */
	private Version<Subject> subVersion;
	

	
	/**
	 * TODO? pre-cached function scope for some function parameter var
	 * 
	 * @param address
	 * @param role
	 * @throws NoSuchVersionException 
	 */
	protected Version(final VersionEnumerable<Subject> address, FunctionallableRole role) throws NoSuchVersionException {
//		super(null, address.isInAST(), address.isGlobal());
//		super(getNonNull(()-> (Subject) address.getVersionSubject()), address.isInAST(), address.isGlobal());
		super(address.getName(), addr-> addr.getSubject(), address.isInAST(), address.isGlobal(), address.getCondGen());
//		type = subject.getType();	// already done by {@link Reference#<init>}
		
		// privately setting address for initiating role
		addr = address;
		init(role);
		
		// publicly setting address fully
//		if (CACHE.containsKey(address)) throwInvalidityException("already registered addressable");
		setAddress(address);
	}

	protected Version(final VersionEnumerable<Subject> address, Subject subject, FunctionallableRole role) throws NoSuchVersionException {
		this(subject, role);
		setAddress(address);
	}
	
	/**
	 * For non-assignable subjects, such as boolean functions, etc.
	 * 
	 * @param subject
	 * @param role
	 * @throws NoSuchVersionException 
	 */
	protected Version(Subject subject, FunctionallableRole role) throws NoSuchVersionException {
		this(subject, role, getNonNull(()-> subject).isGlobal());	// type set by {@link Reference#<init>}
	}
	
	protected Version(Subject subject, FunctionallableRole role, Boolean isGlobal) throws NoSuchVersionException {
		super(subject, subject.isInAST(), isGlobal);
		init(role);
	}
	
	private void init(FunctionallableRole role) throws NoSuchVersionException {
		if (role == null) throwNullArgumentException("role");
		if (!matches(role)) throwTodoException("unmatchable role");
		
		setRole(role);
		setScope(()-> getSubject().getScope());
//		setFunctionScope(subject.getFunctionScope());
	}
	
	static public <Sbj extends Referenceable> Version<Sbj> fromSubversion(
			final VersionEnumerable<Sbj> addr, final FunctionallableRole role,
			TrySupplier<Version<Sbj>, NoSuchVersionException> constructor) 
					throws NoSuchVersionException {
		return from(addr, role, constructor, true, false);
	}
	
	static public <Sbj extends Referenceable> Version<Sbj> fromSuperversion(
			final VersionEnumerable<Sbj> addr, final FunctionallableRole role, 
			TrySupplier<? extends Version<Sbj>, NoSuchVersionException> constructor) 
					throws NoSuchVersionException {
		return from(addr, role, constructor, false, true);
//		Version<Sbj> vdv = addr.getVersion(null), 
//				sub = vdv;
//		while (true) {
//			if (sub instanceof FunctionalVersion) {
//				return (FunctionalVersion) sub;
//			} else {
//				// changing vd's subject from PathVariable to FunctionalPathVariable
//				if (sub == null) return;
//				vdv = sub;
//				sub = sub.getSubversion();
//			}
//		}
	}
	
	static public <Sbj extends Referenceable> Version<Sbj> from(
			final VersionEnumerable<Sbj> addr, final FunctionallableRole role,
			TrySupplier<Version<Sbj>, NoSuchVersionException> constructor) 
					throws NoSuchVersionException {
		return from(addr, role, constructor, false, false);
	}

	@SuppressWarnings("unchecked")
	static private <Sbj extends Referenceable> Version<Sbj> from(
			final VersionEnumerable<Sbj> addr, final FunctionallableRole role,
			final TrySupplier<? extends Version<Sbj>, NoSuchVersionException> constructor, 
			boolean superversionsOld, boolean subversionsOld) 
					throws NoSuchVersionException {
		if (addr == null) throwNullArgumentException("assignable");
		
		Version<Sbj> rootVer = (Version<Sbj>) addr.peekVersion(role);
		if (rootVer == null) {
			if (constructor == null) throwNullArgumentException("constructor");
			addr.setVersion(rootVer = constructor.get());
			
		} else if (constructor != null) try {
			final Version<Sbj> newVer = constructor.get();
			// a[0] is separated from a[1] even if a[0].equals(a[1])
			if (!tests(newVer.equals(rootVer))) {
				// same class or UniversalVersion => different roles
				if (rootVer.getClass().equals(newVer.getClass())
						|| rootVer instanceof UniversalVersion)
					addr.reversion(rootVer = newVer);
				
				/* always return parent version since it's not traverse-able 
				 * from sub-ones
				 */
				else if (superversionsOld) rootVer.subversion(newVer);
				else if (subversionsOld) {
					newVer.subversion(rootVer); rootVer = newVer;}
			}
		
		} catch (ASTException | IncomparableException | NoSuchVersionException e) {
			throwTodoException("unsupported reversioning", e);
		} catch (UncertainPlaceholderException e) {
			e.leave();
		}
		return rootVer;
	}
	
	
	
//	public static boolean findsDeclaration(final String subDecl) {
//		if (DECL_CACHE.contains(subDecl)) return true;
//		for (String decl : DECL_CACHE) if (decl.contains(subDecl)) return true;
//		return false;
//	}
	

	
	@Override
	final protected Object cloneNonConstant() {
		return throwNullArgumentException("non-duplicate address-role pair");
		
//		@SuppressWarnings("unchecked")
//		Version<Subject> clone = (Version<Subject>) super.cloneNonConstant();
//		clone.addr = addr;
//		clone.subVersion = subVersion;	// shallow copy for duplicate version control 
//		if (rhs != null) clone.setAssigner(rhs);
//		return clone;
	}
	
	/**
	 * @param newRole - null means role-unchanged
	 * @return
	 */
	@SuppressWarnings("unchecked")
	@Override
	public <T extends ConditionElement> T cloneIfChangeRole(FunctionallableRole newRole) {
		if (newRole == null) throwNullArgumentException("role");
		
		if (newRole.equals(getThreadRole())) return (T) this;
		return cloneReversion(null, newRole, null);	// this version is NOT allowed to set as default due to a different role
			
//		final Version<Subject> clone = (Version<Subject>) cloneNonConstant();
//		if (clone == this) throwTodoException("non-clonable version");
//
//		clone.role = newRole;	// clone's role is meant to reset
////		clone.setRole(newRole);
//		return (T) clone;
	}

//	public Version<Subject> cloneRename(String newName) {
//		@SuppressWarnings("unchecked")
//		final Version<Subject> nv = (Version<Subject>) cloneNonConstant();
//		nv.setName(newName);
//		nv.setAssigned(false);	// non-declaration clone
//		return nv;
//	}
	
	@SuppressWarnings("unchecked")
	@Override
	public <T extends ConditionElement> T cloneReversion(
			final IASTStatement blockStat, FunctionallableRole role, Version<? extends PathVariable> ver) 
					throws NoSuchVersionException {
		if (role == null) return throwNullArgumentException("role");
		// address-role pair is NOT allowed to be duplicate
		if (getThreadRole().equals(role)) return (T) this;

		final Version<? extends Subject> rv = getPlaceholder().peekVersion(role);
		if (rv != null) return (T) rv;
		
		return ver != null && ver.getThreadRole().equals(role)
				? (T) ver
				: throwNoSuchVersionException(getAddress());
//				: throwNullArgumentException("version supplier");
		
//		final VersionEnumerable<Subject> addr = getAddress();
//		return (T) from(addr, role, ()-> new Version<>(addr, role));
		
//		try {
//			final VersionPlaceholder<Subject> p = getPlaceholder();
//			final ConditionElement pcr = debugGet(()-> p.cloneReversion(blockStat, role, ver));
//			return (T) (pcr == p ? this : pcr);
//			
////		} catch (UncertainPlaceholderException e) {
////			if (ver == null) throwTodoException(e);
////			e.leave();
////			return (T) ver;
//		} catch (Exception e) {
//			return throwUnhandledException(e);
//		}
	}
	

//	@Override
//	protected Expression cacheAssignerIf() {
//		return getNonNull(()-> getAssignable().getAssigner())
//				.cloneReversion(null, peekRole(), null);
//	}

	
	
	/**
	 * @param newRole - null means role-unchanged
	 * @return
	 */
	public void changeRole(FunctionallableRole newRole) {
		if (newRole == null || newRole.equals(role)) return;
		
		setRole(newRole);
		runSkipNull(()-> getSubversion().changeRole(newRole));
	}
	
	
	
	@Override
	public <T> void consumeSkipNullException(
			Consumer<T> con, Supplier<T> inputSup, 
			@SuppressWarnings("unchecked") Supplier<Boolean>... conjTesters) {
		runSkipNull(()-> 
		getAssignable().guard(()-> consumeSkipNullException(con, inputSup, conjTesters)));
	}

	@Override
	public Version<Subject> append(TrySupplier<Version<Subject>, NoSuchVersionException> subVer) {
		if (subVer == null) return this;
			
//		if (subVer instanceof ConstantCountingVersion) return appendConstantCounting();
//		if (getSubject() != subVer.getSubject()) 
//			throw new IllegalArgumentException("Inconsistent subject of sub-version!");
		try {
			assert fromSubversion(addr, getThreadRole(), subVer) == this;
			return fromSubversion(addr, getThreadRole(), subVer);
			
		} catch (NoSuchVersionException e) {
			return throwUnhandledException(e);
		}
	}

	/**
	 * @return
	 * <pre>
	 * 	ver_0								if ver.
	 */
	public Version<Subject> appendConstantCounting() {
//		ConditionElement scope = getScope();	// TODO: delta scope setting?
//		final ConstantCountingVersion VERSION_0 = new ConstantCountingVersion(pv, 0, lv);
		
		// sbj_0 			if sbj;
		final VersionEnumerable<Subject> addr = getAddress();
		if (subVersion == null) return append(()->
				new ConstantCountingVersion<Subject>(0, addr, getThreadRole()));
		
//		// sbj_(n+1)		if sbj_n;
//		else if (subVersion instanceof ConstantCountingVersion) {
//			Version<Subject> newVer = (Version<Subject>) clone();
//			newVer.append(((ConstantCountingVersion<Subject>) subVersion)
//					.increaseCounting());
//			return newVer;
			
		else {
			subVersion.appendConstantCounting();
			return this;
		}
	}
	
	
	
	public FunctionallableRole peekRole() {
		return role;
	}
	
	protected void setRole(FunctionallableRole newRole) {
		if (newRole == null) throwNullArgumentException("new role");
		
		if ((role != null && !role.derives(newRole)) 
				|| (role == null && !matches(newRole))) 
				throwTodoException("unmatchable role");
		
		// checking for both array factories and functional subclass-ing
//		final Assignable asn = getAssignable();
//		if (asn != null && !asn.isThreadPrivate()) 
//			if (newRole.equals(ThreadRole.THREAD1) || newRole.equals(ThreadRole.THREAD2)) 
//				throwInvalidityException("inconsistent role");
		
		role = newRole;
	}
	
	
	
	@Override
	public Expression getAssignerIf() {
		return getAddress().getAssignerIf();
	}
	
//	@Override
//	public void setAssigner(Expression rhs) {
//		AssignableExpression.super.setAssigner(
//				rhs.cloneIfChangeRole(getThreadRole()));
//	}
	
	@Override
	public void setAssigned(Boolean isAssigned) {
		final VersionEnumerable<Subject> addr = getAddress();
		
		// An AST assignable is assigned once internally
		if (addr instanceof Assignable) {
			final Assignable<?> asn = (Assignable<?>) addr;
			final Boolean asnIsA = asn.isAssigned();
			if (isAssigned == asnIsA) return;
			throwTodoException("inconsistent assigned-ness");
		
		} else run(
				()-> ((AssignableExpression) addr).setAssigned(isAssigned),
				e-> throwTodoException(e));
	}
	
	@Override
	public Boolean isAssigned() {
		return getSkipNull(()-> getAddress().isAssigned());
//		return getAssignable() == null
//				? guard(()-> getAddress().isAssigned(), 
//						()-> null)
//				: AssignableExpression.super.isAssigned();
	}


	
//	public void decreaseDimension() {
//		if (type != null) type = type.getPointTo();
////		lv.decreaseDimension();
//	}
	


	public boolean isAddressable() {
		return getAddress() != null;
	}
	
	@SuppressWarnings("unchecked")
	public void setAddress(VersionEnumerable<Subject> addr) {
		if (addr == null) throwNullArgumentException("addressable");
		if (this.addr != null && this.addr != addr) throwTodoException("inconsistent addressable");
		
		this.addr = addr;
		setName(addr.getName());
		consumeSkipNullException(n-> setName(n), ()-> (IName) addr.getASTAddress());	// update IName for any AST addressable
//		setAddressName(addr.getShortAddress());
//		consumeSkipNull(an-> setAddressName(an), ()-> addr.getShortAddress());
		
		if (addr.reversions()) addr.reversion(this);
	}
	
	protected void setAddressName(String addr) {
		if (addr == null || addr.isBlank()) throwNullArgumentException("address");
		final String name = getName();
		if (!name.contains(addr)) setName(name + "_" + addr);
	}
	
	public VersionEnumerable<Subject> getAddress() {
		return addr;
//		for (Entry<Addressable, Version<?>> ve : VERSION_REGISTRY.entrySet())
//			if (ve.getValue() == this) return ve.getKey();
//		return null;
	}
	
	@Override
	public IASTNode getASTAddress() {
		return guard(
				()-> getAddress().getASTAddress(),
				()-> null);
	}

	public Assignable<?> getAssignable() {
		return addr instanceof Assignable ? (Assignable<?>) addr : null;
	}
	
	public NavigableSet<? extends Assignable<?>> getAssigneds() {
		try {
			return get(
					()-> getAssignable().getAssigneds(),
					()-> Collections.emptyNavigableSet());

		} catch (Exception e) {
			return throwTodoException(e);
		}
	}
	
	@SuppressWarnings("unchecked")
	public VersionPlaceholder<Subject> getPlaceholder() {
		return (VersionPlaceholder<Subject>) get(
				()-> getAssignable().getPathVariablePlaceholder(),
				()-> getAddress());
//				e-> throwTodoException(e));
	}
	

	
	@SuppressWarnings("unchecked")
	@Override
	protected <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType) {
		if (refType == null) return throwNullArgumentException(
				"reference type", ()-> Collections.emptySet());

		final Set<T> vrs = new HashSet<>();
		addAllSkipNull(vrs, ()-> 
		getAssignable().getPathVariablePlaceholder().getDirectVariableReferences(refType));

		final Subject sbj = getSubject();
		try {
			if (getClass().asSubclass(refType) != null) {
				if (sbj instanceof Variable) vrs.add((T) this);
				else throwTodoException("non-variable references");
			}  
		} catch (ClassCastException e) {
			addAllSkipNull(vrs, ()-> 
			sbj.getDirectVariableReferences(refType));
		}
		
//		if (subVersion != null) 
//			vrs.addAll(subVersion.getDirectVariableReferences(refType));
		return vrs;
	}

	
	
	@Override
	final public String getID(final SerialFormat format) {
		return getID(format, getThreadRole());
	}
	
	final protected String getID(final SerialFormat format, final FunctionallableRole role) {
		String id = getName() + getIDSuffix(format);
		
		if (role != null) {
			final String roleStr = role instanceof ExtendedRole 
					? ((ExtendedRole) role).toEnumeration()
					: role.toString();
			if (id.endsWith(roleStr)) throwTodoException("duplicate role string");
			
			if (!role.equals(ThreadRole.MASTER)) id += ("_" + roleStr);
//			if (name.endsWith(roleStr)) throwTodoException("duplicate role string");
		}

		return id + getIDSuffixWithoutVersion(format);
//		return getID(format, name, name 
//				+ (isAddressable() ? "" : getIDSuffixWithoutVersion(format)));
		
//		String id = super.getID(format, subjectIdPrefix) + "_";
//		switch (getRole()) {
//		case MASTER:	return id + "m";
//		case NON_MASTER:return id + "nom";
//		case THREAD1:	return id + "1";
//		case THREAD2:	return id + "2";
//		default:		return id + threadRole.toString();
//		}
		
//		return suffix == null ? prefix : (prefix + suffix);
	}
	
	/**
	 * Subversion's ID suffix is provided to avoid redundant 
	 * subject names in combining the sub-version ID's. 
	 * 
	 * @param format
	 * @return
	 */
	@Override
	public String getIDSuffix(SerialFormat format) {
		if (subVersion == null || superversions(null)) return "";
		return "_" + subVersion.getIDSuffix(format);
	}

	/**
	 * @param format - null for generating language-independent ID
	 * @return
	 */
	final public String getIDWithoutVersion(SerialFormat format) {
		assert getSubject() != null;
		return getSubject().getID(format) + getIDSuffixWithoutVersion(format);
	}
	
	final public String getIDSuffixWithoutVersion(SerialFormat format) {
		return "_" + debugGet(()-> getAddress().getShortAddress(format),
				()-> getSubject().getIDSuffix(format));
	}
	
	@Override
	public PlatformType getType() {
		return get(()-> getAssignable().getType(),
				()-> super.getType(),
				e-> throwTodoException(e));
	}
	
	@Override
	public FunctionallableRole getThreadRole() {
		FunctionallableRole r = peekRole();
		final Version<Subject> subV = getSubversion();
		if (subV != null) {
			final FunctionallableRole subR = subV.peekRole();
			if (r.derives(subR)) r = subR;
			else if (!subR.derives(r)) throwTodoException("inconsistent roles");
		}
		return r;
	}
	
	public FunctionallableRole getSubjectRole() {
		return getSubject().getThreadRole();
	}


	
	public Version<Subject> getSubversion() {
		return subVersion;
	}
	
	@SuppressWarnings("unchecked")
//	public <T extends Version<? extends Subject>> T getSubversion(Class<T> type) {
	public <T> T getSubversion(Class<T> type) {
		if (type == null) throwNullArgumentException("version type");
		
		final Version<Subject> sub = getSubversion();
		if (sub == null) return null;
		if (type.isInstance(sub)) return (T) sub;
		return sub.getSubversion(type);
	}
	
	/**
	 * @param newSub
	 * @throws NoSuchVersionException 
	 */
	@SuppressWarnings("unchecked")
	public void subversion(Version<? extends Subject> newSub) {
		if (newSub == this) return;
		if (newSub == null) throwNullArgumentException("subversion");
		
		// name may be changed while subject is constrained
		final String nsName = newSub.getName();
		if (nsName == null || nsName.isEmpty()) 
			throwInvalidityException("no name/ID version");
		final int prefixIdx = nsName.indexOf("_");
		if (!getName().startsWith(
				prefixIdx == -1 ? nsName : nsName.substring(0, prefixIdx))) 
			throwInvalidityException("incompatible sub-version?");

		// unique sub-version
		if (getClass().equals(newSub.getClass()))
			throwInvalidityException("incompatible reocurred sub-version?");
		
		// matching roles
		final FunctionallableRole nr = newSub.getThreadRole();
		if (!matches(nr)) {
			throwNoSuchVersionException(addr, role, nr);
//			newSub = newSub.cloneIfChangeRole(role);
//			log("changing subversion to role " + role);
		}
		
		final Version<Subject> ns = (Version<Subject>) newSub;
		if (superversions(newSub)) {	// ex. ArrayAccessVersion.EnumeratedVersion
			if (subVersion == null || subVersion.derives(ns)) 
				subVersion = ns;
			else subVersion.subversion(newSub);
			
		} else {							// ex. EnumeratedVersion.ArrayAccessVersion
			if (getAddress() != newSub.getAddress()) 
				throwTodoException("inconsistent addresses");
			ns.subversion((Version<? extends Subject>) this);
		}
	}
	
	public boolean subversions(Class<Version<?>> type) {
		return type.isInstance(this) ||
				(subVersion != null && subVersion.subversions(type));
	}
	

	
	/**
	 * For Z3 SMT: FunctionalVersion/ArrayAccessVersion.EnumeratedVersion
	 * TODO? For math notation: ArrayAccessVersion sub-version takes priority as enum -> enum[arr]
	 * 
	 * @param newSub
	 * @return
	 */
	public boolean superversions(Version<? extends Subject> newSub) {
		if (newSub == null) return true;
		if (newSub == this) return false;
		
		// newSub != null
		if (getAddress() != newSub.getAddress()) return false;
		if (!derives(newSub)) return false;
		
		return subVersion == null || 
				(subVersion.superversions(newSub) 
						&& subVersion.superversions(newSub.getSubversion()));
	}
	
	
	
//	@Override
//	public <T extends ConditionElement> T reversion(
//			final IASTStatement blockStat, final ThreadRole role, Version<? extends PathVariable> ver) 
//					throws NoSuchVersionException {
//		try {
//			return getAssignable().reversion(blockStat, role, ver);
//			
//		} catch (NullPointerException e) {
//			return throwTodoException(e);
////		} catch (NoSuchVersionException e) {
//		} catch (Exception e) {
//			return throwUnhandledException(e);
//		}
//	}


	
	@Override
	public <T extends ConditionElement> T substitute(Reference<?> ref1, Reference<?> ref2) {
		if (subVersion != null) subVersion.substitute(ref1, ref2);
		return super.substitute(ref1, ref2);
	}

	
	
	@Override
	public void setName(IName newName) {
		final IASTNode oriAddr = getSkipNull(()-> getAddress().getASTAddress());
		super.setName(newName);
		
		if (oriAddr != null && newName != oriAddr) throwTodoException("inconsistent AST names");
	}
	
	@Override
	final public void setName(String newName) {
		if (newName == null || newName.isEmpty()) throwNullArgumentException("name");
		
//		if (isInAST()) {
//			final ThreadRoleMatchable role = peekRole();
//			if (role != null && newName.contains(role.toString())) throwTodoException("duplicate role string");
//		}
		
		setReferenceableName(newName);
	}

	
	
//	@Override
//	public void setFunctionScope(Supplier<Function> scope) {
//		super.setFunctionScope(scope);
//
//		if (getFunctionScope() != getSubject().getFunctionScope()) 
//			throwTodoException("inconsistent function scope");
//	}

	
	
	final public boolean hasAssignable() {
		return getAssignable() != null;
	}

	public boolean isDeclarator() {
		return false;
	}
	
	@Override
	public boolean isInAST() {
		return getAssignable() != null;
	}

	public boolean isFromAST() {
		return hasAssignable();
	}
	
	@Override
	public boolean isFunctional() {
		return subVersion != null && subVersion.isFunctional();
	}
	
	@Override
	public boolean isThreadPrivate() {
		return get(()-> getAssignable().isDirectiveLocal(),
				()-> super.isThreadPrivate());
	}
	
	
	
	public boolean equalsAssignable(final Version<?> v2) {
		return v2 != null && getAssignable() == v2.getAssignable();
	}
	
	public boolean equalsId(final Version<? extends Subject> v2, final SerialFormat format) {
		return v2 != null && getID(format).equals(v2.getID(format));
	}
	
	public boolean equalsSubject(final Referenceable sbj2) {
		return sbj2 != null && getSubject().equals(sbj2);
	}
	
//	/**
//	 * @return Version value (non-object) based equivalence.
//	 * @see java.lang.Object#equals(java.lang.Object)
//	 */
	/**
	 * @return ID-based equivalence.
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@SuppressWarnings("unchecked")
	@Override
	protected boolean equalsToCache(SystemElement e2) {
		if (e2 == null) return false;
		
		Version<Subject> v2 = (Version<Subject>) e2;
		if (getAddress() != v2.getAddress()) return false; 
		return equalsId(v2, null);
		
//		if (!getSubject().equals(v2.getSubject())) return false;
//		
//		assert role != null;
//		if (!role.equals(v2.role)) return false;
//		
//		Version<? extends Subject> v2sub = v2.subVersion;
//		if (subVersion == null) return v2sub == null;
//		return subVersion.equals(v2sub);
	}
	
	protected List<Integer> hashCodeVars() {
		assert role != null;
		return Arrays.asList(getID(null).hashCode());
//				addr == null ? getSubject().hashCode() : addr.hashCode(),
//				role.hashCode(),
//				subVersion == null ? 0 : subVersion.hashCode());
	}

	
	
	/**
	 * @return false since addr's (assignable's) side-effect depends on its delegate versions' one 
	 * 	circularly and diverged-ly.
	 */
	@Override
	final public boolean suitsSideEffect() {
		return false;
//		return Elemental.getAltNull((TrySupplier<Supplier<VOPConditions>>)
//				()-> getAssignable().getSideEffect(), ()-> super.cacheDirectSideEffect());
	}
	
	
	
	@Override
	protected Boolean cacheConstant() {
		return guard(()-> get(
				()-> ((SystemElement) getAddress()).isConstant(),
				e-> super.cacheConstant()),
				()-> super.cacheConstant());
	}
	
	@Override
	public boolean contains(Expression e) {
		return tests(testsAnySkipNull(
				()-> super.contains(e),
				()-> getSubversion().contains(e)));
	}

	public static boolean contains(Collection<Version<?>> versions, Version<?> target) {
		if (versions == null) throwNullArgumentException("versions");
		if (target == null) throwNullArgumentException("target version");

		if (versions.contains(target)) return true;
		for (Version<?> ver : versions) if (ver.contains((Expression) target)) return true;
		return false;
	}
	
	@Override
	public boolean containsArithmetic() {
		return get(()-> getSubversion().containsArithmetic(),
				e-> false);
	}
	
	@Override
	public Boolean dependsOn(Expression e) {
		// super.dependsOn(e) when !rhs.dependsOn(e) or !getSubversion().dependsOn(e) or null
		return testsAnySkipNull(
				()-> getAssigner().dependsOn(e),
				()-> getSubversion().dependsOn(e),
				()-> super.dependsOn(e));	
	}

	
	
	/**
	 * @param v1s
	 * @param v2s
	 * @return disjunctive version derivation.
	 */
	public static boolean derives(Set<? extends Version<?>> v1s, Set<? extends Version<?>> v2s) {
		if (v1s == null || v2s == null) throwNullArgumentException("version");
		for (Version<?> v1 : v1s)
			for (Version<?> v2 : v2s) if (v1.derives((ThreadRoleMatchable) v2)) return true;
		return false;
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean derives(ThreadRoleMatchable matchable2) {
		return matchable2 instanceof Version
				? derives((Version<? extends Subject>) matchable2)
				: super.derives(matchable2);
	}
	
	/**
	 * Version(PathVariable) derives ArrayAccessVersion(FunctionalPathVariable).
	 * But ArrayAccessVersion(FunctionalPathVariable) does NOT derive Version(PathVariable). 
	 *  
	 * @param ver2
	 * @return
	 */
	@SuppressWarnings("unchecked")
	protected boolean derives(final Version<? extends Subject> ver2) {
		if (ver2 == null) return false;
		if (ver2 == this) return true;
		
		if (!getThreadRole().derives(ver2.getThreadRole()))
			return false;
		if (getAddress() != ver2.getAddress() 
				&& tests(isAssigned()) && tests(ver2.isAssigned()))
			return false;
		
		final Version<? extends Subject> newVerSub = ver2.getSubversion();
//		if (!superversions(newVerSub)) return false;
		if (subVersion != null && !subVersion.derives(newVerSub)) return false;
		
		// checking version derivable 
		final Class<?> vc = getClass(), vcNew = ver2.getClass();
		try {	
			if (vc == vcNew || vcNew.asSubclass(vc) != null) return true;											
		} catch (ClassCastException e) {		// vcNew.asSubclass(vc) == null
			if (getSubversion((Class<Version<? extends Subject>>) vcNew) != null) 
				return true;
		}
		
		// checking subject derivable
		final Referenceable s = getSubject(), sNew = ver2.getSubject();
		if (s != sNew) return false;
		
		final Class<?> sc = s.getClass(), scNew = sNew.getClass();
		try {	
			return sc == scNew || scNew.asSubclass(sc) != null;	
		} catch (ClassCastException e) {		// dnv == true
			return false;
		}
	}
	
	@Override
	public boolean matches(ThreadRoleMatchable matchable2) {
		if (matchable2 == null) throwNullArgumentException("matchable");
		
		// initial matching
		if (matchable2 instanceof Version) return derives(matchable2);
		if (role == null) {
//			if (isZ3ArrayAccess()) return true;
			
			boolean m = true, isTP = isThreadPrivate();
			if (!isTP) m &= 
					!matchable2.equals(ThreadRole.THREAD1) && !matchable2.equals(ThreadRole.THREAD2);
			if (m && isTP) m &= matchable2.equals(ThreadRole.FUNCTION)
					|| matchable2.equals(ThreadRole.THREAD1) || matchable2.equals(ThreadRole.THREAD2);
			if (m && !tests(isConstant())) m &= !matchable2.equals(ThreadRole.CONST);
			return m;
		}

		// update matching
		return role.matches(matchable2);
//		return subVersion != null 
//				? subVersion.matches(role2) 
	}
	
	

	/**
	 * TODO: what's version's negation? Undoing reversion?
	 * 
	 * @see ompca.condition.Expression#negate()
	 */
	public Expression negate() {return null;}
	
	
	
	protected static <T, Subject extends Referenceable> 
	T throwNoSuchSubVersionException(final VersionEnumerable<Subject> venum) 
			throws NoSuchVersionException {
		return throwNoSuchVersionException(venum, "conflict sub-version?");
	}
	
	public static <T, Subject extends Referenceable> 
	T throwNoSuchVersionException(final VersionEnumerable<? super Subject> venum) 
			throws NoSuchVersionException {
		return throwNoSuchVersionException(venum, "non-initialized " + venum);
	}
	
	public static <T, Subject extends Referenceable> T throwNoSuchVersionException(
			final VersionEnumerable<Subject> venum, final String message) 
				throws NoSuchVersionException {
		throw new NoSuchVersionException(venum, message, null);
	}
	
	public static <T, Subject extends Referenceable> T throwNoSuchVersionException(
			final VersionEnumerable<Subject> venum, final Exception cause) 
			throws NoSuchVersionException {
		throw new NoSuchVersionException(venum, null, cause);
	}
	
	public static <T, Subject extends Referenceable> T throwNoSuchVersionException(
			final VersionEnumerable<Subject> venum, final ThreadRoleMatchable role1, final ThreadRoleMatchable role2) 
			throws NoSuchVersionException {
		throw new NoSuchVersionException(venum, role1, role2);
	}
	
	
		
	/**
	 * Subversion-oriented identification
	 */
	@Override
	protected String toNonEmptyString(boolean usesParenthesesAlready) {
		return getID(null);
//		return subVersion == null
//				// default to print ID, which already counts subversion's
//				? getID(null) + "_" + role
//				: subVersion.toNonEmptyString(usesParenthesesAlready);
	}

	/**
	 * @return a non-null (maybe empty however) string.
	 */
	@Override
	public String toZ3SmtString(boolean printsVariableDeclaration, 
			boolean printsFunctionDefinition, boolean isLhs) {
		// for variable declaration w/ versions
		if (printsVariableDeclaration && getSubject() instanceof Variable) {
			
			// for parameter/locals declaration
			if (printsFunctionDefinition) return toZ3SmtLocalDeclaration();
			
			// for variable declaration
			else return toZ3SmtDeclaration();
		}
		
		if (subVersion != null && !enters(METHOD_TO_Z3_SMT_STRING)) {
			enter(METHOD_TO_Z3_SMT_STRING);
			// AAV sub-version takes priority in Z3 SMT: enum[arr] -> (select/store enum arr)
			final String str = subVersion.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition, isLhs);
			leave(METHOD_TO_Z3_SMT_STRING);
			return str;
		}
		// default to print ID, which already counts subversion's
		return super.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition, isLhs);
	}

	public String toZ3SmtType() {
		return getType().toZ3SmtString(true, false);
	}
	
	/**
	 * @return typing using the native Z3 SMT array support
	 */
	public String toZ3SmtTypeDeclaration() {
		return "() " + toZ3SmtType(); 
	}
	
	public String toZ3SmtNameDeclaration() {
		return getID(SerialFormat.Z3_SMT); 
	}
	
	public String toZ3SmtLocalDeclaration() {
		return "(" + getID(SerialFormat.Z3_SMT) 
		+ " " + getType().toZ3SmtString(true, true) + ")";
	}
	
	public String toZ3SmtDeclaration() {
		String name = toZ3SmtNameDeclaration(),
				decl = "(declare-fun " 
				+ name 
				+ " " 
				+ toZ3SmtTypeDeclaration()
				+ ")";
		if (CarryInRangeDegrader.isParam(name)) decl += ("\t\t" + CarryInRangeDegrader.getTagParam());
		return decl;
		
//		Object sbj = this;
//		while (sbj instanceof Array) {
//			str += ("(" + DataType.Int.toZ3SmtString(false, false) + ")");
//			sbj = ((Array) sbj).getPointTo();
//		}
	}

}