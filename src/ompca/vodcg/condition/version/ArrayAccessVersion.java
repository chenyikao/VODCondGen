/**
 * 
 */
package ompca.vodcg.condition.version;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.condition.SerialFormat;
import ompca.vodcg.Assignable;
import ompca.vodcg.SystemElement;
import ompca.vodcg.UncertainPlaceholderException;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.ConditionElement;
import ompca.vodcg.condition.Equality;
import ompca.vodcg.condition.Expression;
import ompca.vodcg.condition.Function;
import ompca.vodcg.condition.PathVariable;
import ompca.vodcg.condition.Variable;
import ompca.vodcg.condition.data.ArithmeticGuard;
import ompca.vodcg.condition.data.ArrayPointer;
import ompca.vodcg.condition.data.ArrayType;
import ompca.vodcg.condition.data.PlatformType;
import ompca.vodcg.condition.data.PointerType;
import ompca.vodcg.condition.version.ThreadRole.ExtendedRole;

/**
 * @author Kao, Chen-yi
 *
 */
public class ArrayAccessVersion<Subject extends Variable> 
extends Version<Subject> 
implements ArgumentMatchable {

	private List<ArithmeticExpression> args = new ArrayList<>();

//	protected ArrayAccessVersion(FunctionalPathVariable var, 
//			IASTArraySubscriptExpression arrayArg,
//			Version<PathVariable> parent, ThreadRoleMatchable role) 
//					throws IllegalArgumentException {
//		super(var, parent.getAddress(), role);
//		
//		if (arrayArg == null) throwNullArgumentException("array expression");
//		init(parent, null, parent.getAssignable());
//		setDimension(arrayArg);
//	}
	
	/**
	 * Incremental constructor by AST arguments.
	 * 
	 * @param parent
	 * @param address
	 * @param role
	 * @throws NoSuchVersionException if its subclass uses invalid 
	 * 	<code>parent</code>, <code>asn</code> or <code>role</code>.
	 */
	protected ArrayAccessVersion(Version<Subject> parent, final VersionEnumerable<Subject> address, FunctionallableRole role) 
			throws NoSuchVersionException {
		this(null, parent, address, role);
	}

	protected ArrayAccessVersion(List<ArithmeticExpression> args,
			Version<Subject> parent, final VersionEnumerable<Subject> ve, 
			FunctionallableRole role) throws NoSuchVersionException {
		super(ve, init(role, args));
		
		init(parent, ve, args);
	}
	
	/**
	 * @param args
	 * @param parent
	 * @param ve
	 * @param role - <em>argument role</em>, which is memory for future argument additions 
	 * 	and may differ from the subject (array variable) role
	 * @throws NoSuchVersionException if its subclass uses invalid 
	 * 	<code>parent</code>, <code>asn</code> or <code>role</code>.
	 */
	protected ArrayAccessVersion(List<ArithmeticExpression> args,
			Version<Subject> parent, final VersionEnumerable<Subject> ve, Subject subject,
			FunctionallableRole role) throws NoSuchVersionException {
		super(ve, subject, init(role, args));
		
		init(parent, ve, args);
	}
	
	private static FunctionallableRole init(FunctionallableRole role, List<ArithmeticExpression> args) {
		if (args == null || args.isEmpty()) return role;
		
		checkArguments(args);
		if (role instanceof ExtendedRole) {
			final ExtendedRole er = (ExtendedRole) role;
			er.setArguments(args);
			return er;
		}
		return role == null
				? throwNullArgumentException("role")
				: role.getBasic().extend(args);
	}
	
	/**
	 * Setting array ID given parent version according to the serialization 
	 * subversion-ing rule.
	 * 
	 * @param args
	 * @param asn 
	 */
	private void init(Version<Subject> parent, final VersionEnumerable<Subject> ve,
			List<ArithmeticExpression> args) {
		if (args != null) {
			for (ArithmeticExpression arg : args) {
				if (arg == null) throwNullArgumentException("argument");
				addArgument(arg);
			}
		}
		
		assert parent == null || parent.getAssignable() != null;
		
		// for both array factories and functional subclass-ing.
//		if (asn.isArray() && !asn.isDeclarator()) throwInvalidityException("not an array declarator");
		
		// updating the back-end array type
//		if (asn != null) setType(getType());
		if (parent != null) setName(parent.getName());
//		if (tests(asn.isAssigned())) setAssigned(rhs, asn.getFirstAssignment());
		
		// array is argument-wise (everywhere) reversion-ed: ve.reversions() || !ve.reversions()
		assert ve != null;
		ve.reversion(this);
	}
	
	
	
	static public <Sbj extends PathVariable> Version<Sbj> from(Version<Sbj> parent, 
			Assignable<Sbj> asn, FunctionallableRole role) 
			throws NoSuchVersionException {
		checkPre(parent, (VersionEnumerable<Sbj>) asn, role);

//		asn = asn.getAssignedOrPreviousNull();
		try {
		final IASTArraySubscriptExpression ase = 
				asn.getEnclosingArraySubscriptExpression();
		final ArrayPointer ap = (ArrayPointer) (ase == null
				? ArrayPointer.from(asn)
				: ArrayPointer.fromRecursively(ase, asn.getRuntimeAddress(), asn.getCondGen()));
		return from(ap.getArguments(), parent, (VersionEnumerable<Sbj>) asn, role);
		
		} catch (ClassCastException e) {
			return throwTodoException(e);
		}
	}
	
	
	
	@SuppressWarnings("unchecked")
	static public <Sbj extends Variable> Version<Sbj> from(List<ArithmeticExpression> args,
			final Version<Sbj> parent, final VersionEnumerable<Sbj> address, 
			FunctionallableRole role) 
					throws NoSuchVersionException {
		checkPre(parent, address, role);
//		if (!asn.isDeclarator()) return from(var, args, parent, asn.getDeclared(), role);
		
		final Version<Sbj> parent_ = parent == null 
				? (Version<Sbj>) address.peekVersion(role)
				: parent;
		final VersionEnumerable<Sbj> pasn = parent_ == null ? 
				address : (VersionEnumerable<Sbj>) parent_.getAddress();
		if (!pasn.equalsAddress(address)) throwInvalidityException("inconsistent addresses");

		if (args == null) {
			if (address instanceof Assignable) args = get(
					()-> (ArrayPointer) ArrayPointer.from((Assignable<PathVariable>) address),
					e-> throwTodoException(e)).getArguments();
			else throwTodoException("unsupported argument-less array");
		}
		final List<ArithmeticExpression> args_ = new ArrayList<>(); 
		if (role.isPrivate()) {
//			if (role instanceof FunctionallableRole && ((FunctionallableRole) role).isFunctional()) 
//				break checkPrivate;
			for (ArithmeticExpression arg : args) {
				if (arg.getThreadRole() != role) arg = arg.cloneReversion(null, role, null);
				args_.add(arg);
			}
//			for (PathVariablePlaceholder argp : arg.getDirectPathVariablePlaceholders())
//				if (argp.isThreadPrivate()) break checkPrivate;
		} else {
			// address.isThreadPrivate() => role.isPrivate()
			if (address.isThreadPrivate()) throwTodoException("inconsistently private");
			args_.addAll(args);
		}
		if (args.size() != args_.size()) throwNullArgumentException("argument");
		
		final ArrayAccessVersion<Sbj> aav = (ArrayAccessVersion<Sbj>) from(address, role, ()-> 
		new ArrayAccessVersion<>(args_, parent_, address, role));
//		aav.setAssigned(asn);
		return aav;
	}
	
	/**
	 * Only for array factories but not functional subclass-ing.
	 * 
	 * @param parent
	 * @param asn
	 * @param role
	 * @throws NoSuchVersionException
	 */
	static private <Sbj extends Variable> void checkPre(Version<Sbj> parent, 
			final VersionEnumerable<Sbj> address, ThreadRoleMatchable role) throws NoSuchVersionException {
		if (role == null) throwNullArgumentException("role");
		if (address == null) {
			if (parent == null) throwNullArgumentException("parent version or assignable");
		} else if (address instanceof Assignable) {
			@SuppressWarnings("unchecked")
			final Assignable<PathVariable> asn = (Assignable<PathVariable>) address;
			if (!asn.isArray()) throwNoSuchVersionException(asn, "not an array");
//			if (asn.isArrayArgument()) throwNoSuchVersionException("argument itself accesses nothing");
			if (tests(asn.isDirectlyFunctional())) throwNoSuchVersionException(asn, "functional array");
		}
	}
	
	
	
//	public Object clone() {
//		ArrayAccessVersion clone = (ArrayAccessVersion) super.clone();
//		if (args != null) clone.args = new ArrayList<>(args);
//		return clone;
//	}

	/**
	 * @return @NotNull
	 */
	protected List<ArithmeticExpression> cloneArguments(
			final IASTStatement blockStat, FunctionallableRole role, Version<? extends PathVariable> ver) {
		final List<ArithmeticExpression> cloneArgs = new ArrayList<>();
		for (ArithmeticExpression arg : getArguments()) {
			if (arg != this) arg = arg.cloneReversion(blockStat, role, null);
			cloneArgs.add(arg);
		}
		return cloneArgs;
	}
	
//	/**
//	 * @param newRole - null means role-unchanged
//	 * @return
//	 */
//	@SuppressWarnings("unchecked")
//	@Override
//	public <T extends Version<Subject>> T cloneIfChangeRole(ThreadRoleMatchable newRole) {
//		// avoiding array_thread1[arg_thread2]
//		if ((isFunctional() || isPrivate()) && newRole.isPrivate()) return super.cloneIfChangeRole(newRole);
//
//		// avoiding unnecessary role-derivation check
//		final Version<?> clone = from(null, getAssignable(), newRole);
//		if (clone == this) throwTodoException("non-clonable version");
//		
//		if (clone instanceof ArrayAccessVersion) {
//			// changing arguments' roles for shared arrays
//			final List<ArithmeticExpression> cloneArgs = new ArrayList<>();
//			for (ArithmeticExpression arg : getArguments()) 
//				cloneArgs.add(arg == this ? 
//						clone : arg.cloneReversion(null, newRole, null));
//			((ArrayAccessVersion<?>) clone).setArguments(cloneArgs);
//		}
//		return (T) clone;
//	}

	public ArrayAccessVersion<Subject> cloneReindex(ArithmeticExpression oldIndex, ArithmeticExpression newIndex) {
		if (oldIndex == null || newIndex == null) throwNullArgumentException("index");
		
		if (tests(oldIndex.isConstant())) return this;
		
		@SuppressWarnings("unchecked")
		final ArrayAccessVersion<Subject> clone = (ArrayAccessVersion<Subject>) clone();
		final List<ArithmeticExpression> cloneArgs = new ArrayList<>();
		for (ArithmeticExpression arg : getArguments()) {
			if (arg == oldIndex) cloneArgs.add(newIndex);
			else cloneArgs.add(arg);
		}
		clone.setArguments(cloneArgs);
		return clone;
	}

	@SuppressWarnings("unchecked")
	@Override
	public <T extends ConditionElement> T cloneReversion(
			final IASTStatement blockStat, FunctionallableRole role, Version<? extends PathVariable> ver) {
		try {
			return (T) super.cloneReversion(blockStat, role, (Version<? extends PathVariable>) this);
			
		} catch (NoSuchVersionException e) {
			return (T) from(cloneArguments(blockStat, role, ver), null, getAddress(), role);
			
		} catch (Exception e) {
			return throwTodoException(e);
		}
	}

	
	
	@Override
	protected Set<ArithmeticGuard> cacheArithmeticGuards() {
		Set<ArithmeticGuard> ags = new HashSet<>(super.cacheArithmeticGuards());
		for (ArithmeticExpression arg : getNonSelfArguments()) 
			ags.addAll(arg.toExpression().getArithmeticGuards());
		return ags;
	}
	
	@Override
	protected Set<Function> cacheDirectFunctionReferences() {
		Set<Function> dfrs = new HashSet<>(super.cacheDirectFunctionReferences());
		for (ArithmeticExpression arg : getNonSelfArguments()) 
			dfrs.addAll(arg.toExpression().getDirectFunctionReferences());
		return dfrs;
	}
	
	@Override
	protected <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType) {
		final Set<T> dvrs = new HashSet<>(super.cacheDirectVariableReferences(refType));
		for (ArithmeticExpression arg : getNonSelfArguments()) 
			dvrs.addAll(arg.toExpression().getDirectVariableReferences(refType));
		return dvrs;
	}
	
	@Override
	protected void cacheDirectSideEffect() {
		super.cacheDirectSideEffect();
		
		try {
		final Assignable<?> dasn = getAssignable().getDeclared();
		@SuppressWarnings("unchecked")
		final ArrayAccessVersion<Subject> ad = (ArrayAccessVersion<Subject>) from(null, dasn, 
				dasn.hasPrivateIterator() 
				? getThreadRole() 
				: (hasArguments() ? ThreadRole.FUNCTION : ThreadRole.MASTER));
		if (ad != this) andSideEffect(()-> Equality.from(this, ad));
		
//		} catch (NoSuchVersionException e) {
		} catch (Exception e) {
			throwTodoException(e);
		}
	}

	

	/**
	 * @param newRole - null means role-unchanged
	 * @return
	 */
	@Override
	public void changeRole(FunctionallableRole newRole) {
		if (isThreadPrivate()) super.changeRole(newRole);
		
		for (ArithmeticExpression arg : getNonSelfArguments())
			for (Version<?> ver : arg.getDirectVariableReferences())
				// ver may be changed (reversion-ed), while arg is not
				if (ver != this && ver.derives(newRole)) 
					((SystemElement) arg).guard(()-> ver.changeRole(newRole));
	}

	protected void checkArguments() {
		checkArguments(getNonSelfArguments());
	}
	
	@SuppressWarnings("deprecation")
	protected static void checkArguments(final List<ArithmeticExpression> args) {
		if (args != null) for (ArithmeticExpression arg1 : args) 
			for (ArithmeticExpression arg2 : args) try {
				if (arg1 == arg2 || checksArguments(arg1, arg2)) continue;
				throwTodoException("unmatchable role");
				
			} catch (UncertainPlaceholderException e) {
				e.leave();
			} catch (Exception e) {
				SystemElement.throwUnhandledException(e);
			}
	}
	
	protected static boolean checksArguments(ArithmeticExpression arg1, ArithmeticExpression arg2) {
		final FunctionallableRole arg1Role = arg1.getThreadRole(),
				arg2Role = arg2.getThreadRole();
//	boolean isM = true;
//		if (cr == null) {
//			// matching function or thread-private roles
//			final boolean isL = getAssignable().isLoopConditional();
//			switch (arrayRole) {
//			case CONST:
//			case MASTER:
//			case NON_MASTER:	isM = !isL; break;
//			case FUNCTION:
//			case THREAD1:
//			case THREAD2:		isM = isL; break;
//			default:			throwTodoException("unsupported role");
//			}
//			cr = arrayRole;
//		}
		
//		if (arrayRole.derives(arg1Role)) {
//			continue;
//		}
		// cases of array (shared or thread-private) with thread-private arguments
		if (arg1Role.derives(arg2Role) || arg2Role.derives(arg1Role)) {
			/* ..._FUNCTION[..._THREAD1][..._FUNCTION][...]
			 * 	=> ..._FUNCTION[..._THREAD1][..._THREAD1][...]
			 */
//			if (av.getAssignable().isThreadPrivate()) av.changeRole(argsRole);
			return true;
		}
		/* ..._FUNCTION[..._THREAD1][..._THREAD2][...]
		 * 	=>	unmatchable role
		 */
		return false;
	}
	
	
	
	@Override
	public String getIDSuffix(SerialFormat format) {
		String suffix = super.getIDSuffix(format);
		for (ArithmeticExpression arg : getNonSelfArguments()) 
			suffix += ("_" + arg.toNonEmptyString());
		return suffix;
	}

	@Override
	public ThreadRole getSubjectRole() {
		return getSkipNull(()->
		getAssignable().initRole());
	}

//	@Override
//	public IASTStatement getPrivatizingBlock() {
//		return get(()-> ArrayPointer.from(getAssignable()).getPrivatizingBlock(),
//				// for possibly non-array subclasses, like FunctionalVersion's
//				()-> super.getPrivatizingBlock());
//	}
	
	

//	/**
//	 * @return the AST type of the back-end array pointer, e.g. a[], a[][] and a[][][], etc.
//	 */
//	@Override
//	public PlatformType getType() {
//		return get(()-> getReferenceableType(),
//				()-> ArrayType.from(getAddress(), getAstArguments()));
//	}

	public PlatformType getCodomainType() {
		return getPointerType().getPointToEndType();
	}
	
	/**
	 * @return a truly non-AST array pointer type
	 */
	public PointerType getPointerType() {
		return ArrayType.from(ArrayPointer.from(getAssignable()));
	}

	
	
	public ArithmeticExpression getNonSelfArgument(int index) {
		final ArithmeticExpression arg = getArguments().get(index);
		return arg == this ? null : arg;
	}
	
	/**
	 * @return @NotNull
	 */
	public List<ArithmeticExpression> getNonSelfArguments() {
		final List<ArithmeticExpression> args = new ArrayList<>();
		for (ArithmeticExpression sarg : getArguments()) 
//			if (sarg != this && !(sarg instanceof Version && equalsAssignable((Version<?>) sarg)))
			if (sarg != this)
				args.add(sarg);
		return Collections.unmodifiableList(args);
	}
	
	/**
	 * @return @NotNull
	 */
	public List<ArithmeticExpression> getAstArguments() {
		return getArguments();
	}

	public ArithmeticExpression getAstArgument(int index) {
		return getAstArguments().get(index);
	}
	
	/**
	 * @return @NotNull
	 */
	public List<ArithmeticExpression> getArguments() {
		return args != null
				? Collections.unmodifiableList(args)
				: Collections.emptyList();	// args == null when it's at superclass construction time 
	}
	
	public ArithmeticExpression getArgument(int index) {
		return getArguments().get(index);
	}
	
	/**
	 * TODO? synchronize with thread-role arguments
	 * @param arg
	 * @return
	 */
	private boolean addArgument(ArithmeticExpression arg) {
		if (arg == null) return throwNullArgumentException("argument");
		
		try {
//			if (arg instanceof VariablePlaceholder) 
//				return addArgument((VariablePlaceholder<PathVariable>) arg);
//			
//			checkArgumentRole(arg);
			assert args != null;
			// synchronizing thread role - array_thread1[arg_thread1], array_non_master[arg_non_master]
			final FunctionallableRole role = getThreadRole();
			return args.add(role.isPrivate()
					? arg.cloneReversion(null, role, null)
					: arg);

		} catch (Exception e) {
			return throwTodoException(e);
		}
	}
	
//	private boolean addArgument(VariablePlaceholder<PathVariable> arg) {
//		assert arg != null && args != null;
//		try {
//			return args.add(getNonNull(()->
//			arg.getVersion(getThreadRole())));
//			
//		} catch (Exception e) {
//			return throwTodoException(e);
//		}
//	}
	
	public boolean hasArguments() {
		return !getArguments().isEmpty();
	}
	
	public void setArguments(List<ArithmeticExpression> args) {
		this.args = matchArgumentsTo(args, getThreadRole());
	}
	
	/**
	 * @param args
	 */
	public void setArguments(ArithmeticExpression[] args) {
		setArguments(Arrays.asList(args));
	}
	

	
//	/**
//	 * Setting AST-defining dimensions without changing types.
//	 * 
//	 * @param dim
//	 */
//	private void setDimension(IASTArraySubscriptExpression dim) {
//		assert dim != null;
//		
//		IASTInitializerClause arg = dim.getArgument();
//		if (arg == null) return;
//		
//		final Expression arge = Expression.fromRecursively(arg, getCondGen());
//		if (arge instanceof ArithmeticExpression) args.add(0, (ArithmeticExpression) arge);
//		else throwTodoException("unsupported arithmetic expression");
//		
//		// setting multiple dimensions
//		if (arg instanceof IASTArraySubscriptExpression) 
//			setDimension((IASTArraySubscriptExpression) arg);
//	}
	
	
	
	/**
	 * Serialized at the top level for Z3-SMT formats.
	 * @param sub
	 * @return
	 */
	@Override
	public boolean superversions(Version<? extends Subject> sub) {
		return true;
	}
	
	@Override
	protected boolean derives(final Version<? extends Subject> newVer) {
		return newVer != null 
				&& getAddress().derives(newVer.getAddress())
				&& super.derives(newVer);
	}
	
	@Override
	public Boolean dependsOn(Expression e) {
		for (ArithmeticExpression arg : getNonSelfArguments())
			if (arg.toExpression().dependsOn(e)) return true;
		return super.dependsOn(e);
	}

	public boolean dependsOn(Variable v) {
		for (ArithmeticExpression arg : args) {
			boolean is = arg.toExpression().dependsOn(v);
			if (is) return true;
		}
		return false;
	}
	
	@Override
	public boolean isZ3ArrayAccess() {
		return true;
	}
	
//	@Override
//	public boolean derivesFrom(Version<FunctionalPathVariable> oldVersion) {
//		return true;
//	}

	@Override
	public boolean matches(ThreadRoleMatchable matchable2) {
		if (matchable2 instanceof Version) try {
			if (getAssignable().getEnclosingCanonicalLoopIterator() 
					== ((Version<?>) matchable2).getAssignable())
				// ..._MASTER(..._FUNCTION/THREADx, ..._FUNCTION/THREADx, ...)
				return getThreadRole().derives(matchable2);
					
		} catch (NullPointerException e) {
		}
		
		// arguments may be not ready at super-class construction time
		for (ArithmeticExpression arg : getNonSelfArguments())
			if (!arg.matches(matchable2)) return false;
		return peekRole() == null
				? true	// array arguments may be either thread-shared or thread-private
				: super.matches(matchable2);
	}
	
	/**
	 * Matching and setting arguments at once.
	 */
	@SuppressWarnings("unchecked")
	@Override
	public <T> List<T> matchArgumentsTo(
			final List<T> args, final ThreadRoleMatchable newRole) {
		assert peekRole() != null;
		if (getThreadRole().derives(newRole)) {
			final List<T> margs = super.matchArgumentsTo(args, newRole);
			this.args = (List<ArithmeticExpression>) margs;
			return margs;
		}
		return throwTodoException("underivable roles");
	}
	
	
	
//	/**<pre>
//	 * @return the inductive condition of serial iteration schedule:
//	 * 	[Initial/pre-condition]
//	 * 	<code>
//	 * 	</code>
//	 * 
//	 * 	[Closure condition]
//	 * 	<code>
//	 * 	forall lb <= (i) <= ub, f(i) = ...
//	 * 	</code>
//	 * 
//	 * 	[Post condition]
//	 * 	<code>
//	 * 	</code>
//	 */
//	@Override
//	public Proposition toProposition() {
//		return generateRaceAssertion();
//	}
	
	
	
//	@Override
//	public String disambiguateString(SerialFormat format, 
//			String originalTerm, String disambiguousTerm) {
//		return format == null 
//				? super.disambiguateString(format, originalTerm + "[", disambiguousTerm)
//				: super.disambiguateString(format, originalTerm, disambiguousTerm);
//	}

	
	
	@Override
	protected String toNonEmptyString(boolean usesParenthesesAlready) {
		String argString = new String();
		for (ArithmeticExpression arg : args) argString += ("[" + arg.toString() + "]");
		return getID(null) + argString;
	}



	public String toZ3SmtCodomainType() {
		return get(()-> getCodomainType().toZ3SmtString(true, false),
				e-> throwTodoException(e));
	}

	public String toZ3SmtLocalParamsDeclaration(boolean printsParamNames) {
		String decl = new String();
		for (ArithmeticExpression arg : getNonSelfArguments()) 
//		for (ArithmeticExpression arg : getAstArguments()) 
			decl += ((printsParamNames 
					? arg.toZ3SmtString(true, true, false) 
					: arg.getType().toZ3SmtString(true, false)) + " ");
		return decl;
	}
	
	/**
	 * @return a role-independent array name in Z3 SMT format
	 */
	@Override
	public String toZ3SmtNameDeclaration() {
		return getID(SerialFormat.Z3_SMT, null); 
	}
	
	/**
	 * @return typing using the native Z3 SMT array support
	 */
	@Override
	public String toZ3SmtTypeDeclaration() {
		return "() (Array " 
				+ toZ3SmtLocalParamsDeclaration(false)
				+ toZ3SmtCodomainType() + ")"; 
	}

	/**
	 * @see ompca.condition.Equality#toZ3SmtString(boolean, boolean, boolean)
	 */
	@Override
	public String toZ3SmtString(boolean printsVariableDeclaration, 
			boolean printsFunctionDefinition, boolean isLhs) {
		// Z3 native array support shows no function or thread-private argument roles
		final boolean isZ3A = isZ3ArrayAccess();
		// isZ3ArrayAccess() may be overridden by functional loop iterator versions
		if (printsVariableDeclaration || !isZ3A) 
			return super.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition, isLhs);
			
		final boolean isA = tests(isAssigned()) && isLhs;
		final String array = toZ3SmtNameDeclaration();
		/* 
		 * (store a i v) returns a new array identical to a, but on position i it contains the value v.
		 * (https://rise4fun.com/Z3/tutorial/guide)
		 */
		String str = "(", args = new String();
		if (isA) {
			final VersionEnumerable<Subject> pArray = getPlaceholder().previousOrUnambiguousAssigned();
			if (pArray == null) throwNullArgumentException("array");
			str += ("= (store " + pArray.getVersion(getThreadRole()).toZ3SmtNameDeclaration());
		} else 
			str += ("select " + array);
					
		// array indices
		for (ArithmeticExpression arg : getArguments()) 
			args += debugCallDepth(()-> " " + arg.toZ3SmtString(false, printsFunctionDefinition, isLhs));
		str += args; 
		
		if (isA) {
			final String asner = getAssigner().toZ3SmtString(false, false, isLhs);
			str += (" " + asner + ") " + array);
		}
		return str + ")";
	}

}