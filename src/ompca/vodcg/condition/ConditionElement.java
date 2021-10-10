package ompca.vodcg.condition;

import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.function.Supplier;

import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.core.runtime.CoreException;

import ompca.Elemental;
import ompca.Emptable;
import ompca.condition.SerialFormat;
import ompca.vodcg.ASTAddressable;
import ompca.vodcg.ReenterException;
import ompca.vodcg.SystemElement;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.data.ArithmeticGuard;
import ompca.vodcg.condition.data.Pointer;
import ompca.vodcg.condition.data.PointerType;
import ompca.vodcg.condition.version.ArgumentMatchable;
import ompca.vodcg.condition.version.FunctionallableRole;
import ompca.vodcg.condition.version.NoSuchVersionException;
import ompca.vodcg.condition.version.ThreadRoleMatchable;
import ompca.vodcg.condition.version.Version;
import ompca.vodcg.parallel.ThreadPrivatizable;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
abstract public class ConditionElement extends SystemElement 
implements ArgumentMatchable, Emptable, Cloneable, ThreadPrivatizable {

	static private final Method METHOD_GET_DIRECT_FUNCTION_REFERENCES = 
			Elemental.getMethod(ConditionElement.class, "getDirectFunctionReferences");
	private static final Method METHOD_GET_FUNCTION_REFERENCES = 
			Elemental.getMethod(ConditionElement.class, "getFunctionReferences", Set.class);
	private final static Method METHOD_GET_ARITHMETIC_GUARDS = 
			Elemental.getMethod(ConditionElement.class, "getArithmeticGuards");
	private static final Method METHOD_GET_SCOPE = 
			Elemental.getMethod(ConditionElement.class, "getScope");
//	private static final Method METHOD_IS_GLOBAL = 
//			Elemental.getMethod(ConditionElement.class, "isGlobal");
	private static final Method METHOD_TO_STRING = 
			Elemental.getMethod(ConditionElement.class, "toString");
//	private static final Method METHOD_REDUCE_ONCE = 
//			Elemental.getMethod(ConditionElement.class, "reduceOnce");
	
	
	
	// for cache/registry
	/**
	 * A class own set to avoid {@link UnsupportedOperationException}.
	 */
	final private Set<ArithmeticGuard> ags = new HashSet<>();
	
	private Set<Function> functionRefs = null;
	private Set<Function> directFunctionRefs = null;
	
	private Supplier<? extends ConditionElement> scope	= null;
	private Supplier<Function> funcScope				= null;
	private boolean resetsFuncScope = true;
	
	
	
	/**
	 * @param scopeManager
	 */
	protected ConditionElement(final ASTAddressable rtAddr, VODCondGen scopeManager) {
		super(rtAddr, scopeManager);
	}

//	@Override
//	public Object clone() {
//		Condition clone = (Condition) super.clone();
//		clone.ags.addAll(ags);
//		return clone;
//	}

	public <T extends ConditionElement> T cloneIfChangeRole(final FunctionallableRole role) {
		return cloneReversion(null, role, null);
	}
	
	/**
	 * @param <T>
	 * @param blockStat
	 * @param role
	 * @param ver
	 * @return a thread-private version explicitly expressing element.
	 * @throws NoSuchVersionException
	 */
	@SuppressWarnings("unchecked")
	public <T extends ConditionElement> T cloneReversion(
			IASTStatement blockStat, final FunctionallableRole role, final Version<? extends PathVariable> ver) 
					throws NoSuchVersionException {
		if (tests(isConstant())) return (T) this;
		if (role == null || role.derivesBasic(getThreadRole())) return (T) this;
//		if (role != null && (role.isShared() || getThreadRole().equals(role))) return (T) this;
		if (blockStat == null) blockStat = getPrivatizingBlock();
		
		final T newCe = (T) clone();
		if (newCe == this) Version.throwNoSuchVersionException(null, "non-clonable");
		
		for (VariablePlaceholder<?> vp : newCe.getDirectVariablePlaceholders()) try {
			if (newCe == vp) continue;	
			final Reference<?> pvpv = vp.cloneReversion(blockStat, role, null);	// vp.address != ver.address
			newCe.substitute(vp, pvpv);
			
		} catch (ReenterException e) {
			continue;
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
		
//		for (Version<?> v : newCe.getDirectVariableReferences()) {
//			assert newCe != v;	// since Version overrides
//			if (v.getThreadRole().equals(role)) continue;
//			final Version<?> vv = v.cloneIfChangeRole(role);
//			newCe.substitute(v, vv);
//		}
		return newCe;
	}
	
	@Override
	public ArgumentMatchable matchTo(final ThreadRoleMatchable newRole) {
		return newRole instanceof FunctionallableRole
				? cloneReversion(null, (FunctionallableRole) newRole, null)
				: throwUnsupportedRoleException();
	}
	

	
	/**
	 * @param format - null for generating language-independent ID
	 * @return
	 */
	public String getID(final SerialFormat format) {
		final String name = getName();
		return getID(format, name, name + "_" + getIDSuffix(format));
	}
	
	protected String getID(final SerialFormat format, 
			final String originalTerm, final String disambiguousTerm) {
		return disambiguateString(format,
				// TODO? using separate dis-ambiguous strings for different formats
				originalTerm, disambiguousTerm);
	}
	
//	abstract public String getIDSuffix(SerialFormat format);
	public String getIDSuffix(SerialFormat format) {
		return throwTodoException("not identifiable element");
	}
	
	public String getName() {
		return throwTodoException("not namable element");
	}
	
	
	
	abstract protected Set<ArithmeticGuard> cacheArithmeticGuards(); 
//	{
//		return sideEffect == null 
//				? Collections.emptySet() 
//				: sideEffect.getArithmeticGuards();
//	}
	
	public boolean hasGuards() {
		return !ags.isEmpty();
	}
	
	public boolean hasPositiveGuards() {
		for (ArithmeticGuard ag : ags) 
			if (tests(ag.isPositive())) return true;
		return false;
	}
	
	public boolean hasPositiveOrZeroGuards() {
		for (ArithmeticGuard ag : ags) 
			if (tests(ag.isPositiveOrZero())) return true;
		return false;
	}
	
	public boolean hasNegativeGuards() {
		for (ArithmeticGuard ag : ags) 
			if (tests(ag.isNegative())) return true;
		return false;
	}
	
//	/**
//	 * hasGuards => variable/non-constant
//	 * 
//	 * @param hasPositive
//	 * @param hasNegative
//	 * @return
//	 */
//	protected boolean hasGuards(final boolean hasPositive, final boolean hasNegative) {
//	}

	public void addGuard(ArithmeticGuard guard) {
		if (guard == null) throwNullArgumentException("arithmetic guard");
		if (guard == this) throwNullArgumentException("non-self guard");
		ags.add(guard);
	}
	
	public void addGuards(Set<ArithmeticGuard> guards) {
		if (guards == null) throwNullArgumentException("arithmetic guard");
		for (ArithmeticGuard g : guards) addGuard(g);
	}
	
	/**
	 * @return a non-null set
	 */
	final public Set<ArithmeticGuard> getArithmeticGuards() {
		try {
			guardThrow(()-> 
			addAllSkipNull(ags, ()-> cacheArithmeticGuards()),
			METHOD_GET_ARITHMETIC_GUARDS);
			
		} catch (ReenterException e) {
			e.leave();
		} catch (Exception e) {
			throwUnhandledException(e);
		}
		
		if (this instanceof ArithmeticGuard && ags.contains(this)) 
			throwInvalidityException("non-self guard");
		return ags;
	}
	
	protected abstract <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType);
	
	final public Set<? extends PathVariablePlaceholder> 
	getDirectPathVariablePlaceholders() {
		return getDirectVariableReferences(PathVariablePlaceholder.class);
	}
	
	@SuppressWarnings("unchecked")
	final public Set<? extends VariablePlaceholder<?>> 
	getDirectVariablePlaceholders() {
		return (Set<? extends VariablePlaceholder<?>>) getDirectVariableReferences(VariablePlaceholder.class);
	}
	
	@SuppressWarnings("unchecked")
	final public Set<Version<?>> getDirectVariableReferences() {
		return (Set<Version<?>>) getDirectVariableReferences(Version.class);
	}
	
	/**
	 * @return Neither null nor indirect {@link Pointer}s.
	 */
	@SuppressWarnings("unchecked")
	final public <T> Set<? extends T> getDirectVariableReferences(
			Class<T> refType) {
		return debugGet(()-> guard(()-> get(()-> (Set<T>) cacheDirectVariableReferences(refType),
				// null to empty
				()-> Collections.emptySet(),
				e-> throwTodoException(e)),
				
				// reentering empty for continuing the initial entering without duplicates
				()-> Collections.emptySet()));
	}
	
	public Set<Version<?>> getVariableReferences() {
		return (Set<Version<?>>) getDirectVariableReferences();
	}
	
	final public <T> Set<T> getNonConstVariableReferences(Class<T> refType) {
		final Set<T> ncvrs = new HashSet<>();
		for (T v : getDirectVariableReferences(refType)) {
			if (v instanceof SystemElement 
					&& tests(((SystemElement) v).isConstant())) continue; 
			ncvrs.add(v);
		}
		return ncvrs;
	}
	
	abstract protected Set<Function> cacheDirectFunctionReferences();
	
	final public Set<Function> getDirectFunctionReferences() {
		if (directFunctionRefs == null) {
			if (!enters(METHOD_GET_DIRECT_FUNCTION_REFERENCES)) {
				enter(METHOD_GET_DIRECT_FUNCTION_REFERENCES);
				directFunctionRefs = cacheDirectFunctionReferences();
				leave(METHOD_GET_DIRECT_FUNCTION_REFERENCES);
			}
		}
		return directFunctionRefs == null 
				? Collections.<Function>emptySet() : directFunctionRefs;
	}
	
	/**
	 * @param refs - is passed by pointer value and NOT altered if 
	 * 	it's null. 
	 * @return
	 * @throws InterruptedException 
	 * @throws CoreException 
	 */
	final public Set<Function> getFunctionReferences(Set<Function> refs) {
		if (enters(METHOD_GET_FUNCTION_REFERENCES)) return refs;
		
//		FUNCTION_REFS.clear();
		Set<Function> subRefs = null, subRefs2;
		
		if (functionRefs == null) {
			functionRefs = getDirectFunctionReferences();
			if (functionRefs == null) return refs;
			
			// updating indirect references
			int preSize, postSize = -1;
			do {
				preSize = functionRefs.size();
				// gathering f's own function references despite of refs
//				synchronized (funcRefs) {
				for (Function f : functionRefs) {
					enter(METHOD_GET_FUNCTION_REFERENCES);
					subRefs2 = f.getFunctionReferences(subRefs);
					leave(METHOD_GET_FUNCTION_REFERENCES);
					if (subRefs == null) 
						subRefs = subRefs2;
					else if (subRefs2 != null && subRefs != subRefs2) 
						subRefs.addAll(subRefs2);
				}
//				}
				if (subRefs != null && !subRefs.isEmpty()) {
					functionRefs.addAll(subRefs);
					postSize = functionRefs.size();
				}
			} while (postSize > preSize);
		}
		
//		TODO? Set<VariableVersionDelegate> vds = getVariableReferences();
//		if (vds != null) for (VariableVersionDelegate vd : vds) {
//			ConditionElement ce = vd.getScope();
//			if (ce instanceof Function) {
//				Function f = (Function) ce;
//				if (refs == null) refs = 
//						Collections.synchronizedSortedSet(new TreeSet<>(f));
//				refs.add(f);
//			}
//		}
		
		assert functionRefs != null;
		if (refs == null) refs = new HashSet<>(functionRefs);// guaranteeing an immutable FUNCTION_REFS
		else if (refs != functionRefs) refs.addAll(functionRefs);
		
		return refs;
	}
	
	public abstract Set<Pointer> getPointers();
	
	
	
	public VODCondGen getScopeManager() {
		return getCondGen();
	}
	
	/**
	 * Common scope:
	 * Global -> Function -> Proposition/Relation
	 * 
	 * @param ce2
	 * @return
	 */
	public ConditionElement getCommonScope(ConditionElement ce2) {
		if (ce2 == null) return null;
		return getCommonScope(getScope(), ce2.getScope());
	}
	
	final protected static ConditionElement getCommonScope(
			ConditionElement scope1, ConditionElement scope2) {
		if (scope1 == scope2) return scope1;
		
		if (scope1 != null && scope1.equalsGlobal()) return scope1;
		if (scope2 != null && scope2.equalsGlobal()) return scope2;
		
		// assert scope1 != scope2 != GlobalScope;
		final ConditionElement s1s = scope1 == null ? null : scope1.getScope(),
				s2s = scope2 == null ? null : scope2.getScope();
		if (s1s == scope1) {
			if (s2s == scope2 || s2s == null) return scope1;
		} else {
			// s1s != scope1
			if (s2s == null) return getCommonScope(s1s, scope2);
		}
		return getCommonScope(s1s, s2s);
	}
	
	/**
	 * Assuming no null (default) functions and all functions are top-level and there's NO nested functions.
	 * 
	 * @param f1
	 * @param f2
	 * @return
	 */
	protected static Function getCommonFunctionScope(Function f1, Function f2) {
		if (f1 == null) return f2;
		if (f2 == null) return f1;
		
		switch (Function.compareIn(f1, f2)) {
		case isAfter:	return f2;
		case isBefore:
		case equals:
		default:		return f1;
		}
	}
	
	/**
	 * Lazy scope setting framework.
	 * 
	 * @return
	 */
	final public ConditionElement getScope() {
		ConditionElement s = null;
		if (scope != null) {
			s = scope.get();
			if (s instanceof Function) {
				final Function fs = (Function) s;
				setFunctionScope(()-> fs);
			}
			return s;
		}
		
		if (!setsGlobalScope()) {
			assert !equals(scope.get()) || this instanceof VODConditions;
			guardSkipException(()-> {
			setScope(()-> cacheScope());
			if (scope == null) setScope(()-> getFunctionScope());}, 
					METHOD_GET_SCOPE);
		}
		return getScope();
	}
	
	/**
	 * No tangling with global scope setting.
	 * 
	 * @return
	 */
	@Override
	protected Boolean cacheGlobal() {
		if (tests(super.cacheGlobal())) return true;
		if (enters()) return null;
		if (getFunctionScope() != null) return false;
		
		/* getScope() instanceof Function && getScope().isGlobal			=> !isGlobal
		 * getScope() instanceof ParallelCondition && getScope().isGlobal 	=> isGlobal
		 */
		return !testsNot(guardSkipException(()-> 
		getScope().equalsGlobal()));	
	}
	
	protected ConditionElement cacheScope() {
		return null;
	}
	
	final public void fillScope(ConditionElement newScope) {
		if (scope == null) setScope(()-> newScope);
	}
	
	/**
	 * @param newScope - Null means unknown except for 
	 * 	{@link VODCondGen}-wise global scope.
	 */
	final public void setScope(Supplier<? extends ConditionElement> newScope) {
		if (newScope != null) {
			scope = newScope;
			return;
		}

		// lazy scope setting
		assert newScope == null;
		if (!setsGlobalScope()) throwNullArgumentException("new scope");
	}
	
	/**
	 * Resetting parent (container) properties, such as (function) scopes.
	 * 
	 * @param scope
	 * @param fScope
	 */
	public void setScope(ConditionElement scope, Function fScope) {
		setScope(()-> scope);
		setFunctionScope(()-> fScope != null 
				? fScope 
				: (scope == null ? null : scope.getFunctionScope()));
	}
	
	final public Function getFunctionScope() {
		if (!resetsFuncScope) {
			if (funcScope != null) {
				final Function fs = funcScope.get();
				if (fs != null) return fs;
			}
		}
		
		Function fs2 = cacheFunctionScope();
		if (fs2 != null) setFunctionScope(()-> fs2);
		return fs2;
	}
	
	protected Function cacheFunctionScope() {
		if (tests(isConstant())) return null;

		Function fs = funcScope == null ? null : funcScope.get();
		if (enters(METHOD_GET_SCOPE)) return fs;
		
		enter(METHOD_GET_SCOPE);
		ConditionElement scope = getScope();
		if (scope instanceof Function) 
			fs = getCommonFunctionScope(fs, (Function) scope);
		else if (scope != null && !equals(scope)) 
			fs = getCommonFunctionScope(fs, scope.getFunctionScope());
		leave(METHOD_GET_SCOPE);
		return fs;
	}
	
	/**
	 * @param scope - no (null) function scopes implies a global scope
	 */
	public void setFunctionScope(Supplier<Function> scope) {
		funcScope = scope;
		resetsFuncScope = false;
//		if (scope == null) setScope(getScopeManager().getGlobalScope());
	}
	
//	private void setFunctionReferences(Set<Function> refs) {
//		functionRefs.put(
//				this, 
//				// guaranteeing an immutable FUNCTION_REFS
//				refs == null ? refs : new HashSet<>(refs));
//	}
	
	
	
	@Override
	public void setGlobal() {
		super.setGlobal();
//		if (!setsGlobalScope()) throwTodoException("inconsistent global-ness");
	}

	
	
	/**
	 * Resetting children properties, such as hash code and function references.
	 */
	protected void setDirty() {
		ags.clear();
		functionRefs = null;
		directFunctionRefs = null;
		resetsFuncScope = true;
//		scope = null;		// scope may be just set before
		
//		if (!sesupCache.isEmpty()) throwTodoException("overthrowing original side-effect");
//		resetSideEffect();
		
		super.setDirty();
	}
	
//	protected void setDirtyExcept(Function fScope) {
//	}
	
//	/**
//	 * Mutable reduction.
//	 * 
//	 * Removing the redundant operator (e.g. {@link Operator}) and 
//	 * merging the redundant operands if possible.
//	 * 
//	 * @return an equivalent simplified {@link Relation}.
//	 */
//	@SuppressWarnings("unchecked")
//	protected ConditionElement reduceOnce() {
//		if (sesupCache != null) sesupCache.reduce(METHOD_REDUCE_ONCE);	
//		super.reduceOnce();
//		return this;
//	}
	
	

	/**
	 * A mutable operation.
	 * 
	 * @param ref1
	 * @param ref2
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public <T extends ConditionElement> T substitute(Reference<?> ref1, Reference<?> ref2) {
		return (T) (ref1 == this ? ref2 : this);
	}
	
	
	
//	private Proposition initSideEffect() 
//			throws CoreException, InterruptedException {
//		PointableType ptType = this instanceof Pointer 
//				? ((Pointer) this).getPointTo() : getType();
//		if (ptType instanceof DataType) switch ((DataType) ptType) {
//		case Bool:
//			return new Equality(
//					this, Proposition.getTrue(getScopeManager()), getScope());
//		case Pointer:
//		case Real:
//		case Char:
//		case Int:
//		case Array:
//		default:
//		}
//		return null;
//	}
	
	/**
	* For a SideEffectElement container.
	 * @param <T>
	 * @param newSe
	 * @return
	 */
	@SuppressWarnings("unlikely-arg-type")
	protected <T extends SideEffectElement> boolean suitsSideEffect(T newSe) {
		if (newSe == null) throwNullArgumentException("new side-effect");	// TODO?{sideEffect = null; return false;}
		
		if (equals(newSe)) return false;
		if (!suitsSideEffect()) {
			throwTodoException("Such side-effect is NOT necessary: " + newSe);
			return false;
		}
		return true;
	}
	
	/**
	 * For a SideEffectElement container.
	 * @return true if <em>unconditionally</em> suits side-effect.
	 */
	public boolean suitsSideEffect() {return true;}
	

	
//	public boolean containsEmpty() {
//		if (super.containsEmpty()) return true;
//		// recursive structure means containing non-empty
////		try {if (isConstant()) return false;} catch (IllegalStateException e) {return false;}
//		if (startsCircularTraverse) return false;
//		
//		startsCircularTraverse = true;
//		boolean isRecursivelyEmpty = sideEffect != null && sideEffect.containsEmpty();
//		startsCircularTraverse = false;
//		return isRecursivelyEmpty;
//	}
	
	/**
	 * @return true if this element contains any element or itself that could generates 
	 * illegally empty (path) condition.
	 */
	public boolean containsEmpty() {
		return isEmpty();
	}
	
	abstract public boolean isEmpty();
	
	
	
	/**
	 * @return true if the global scope is changed.
	 */
	private boolean setsGlobalScope() {
		if (debugTests(()-> isGlobal())) {	
			// including global VOPConditions scope if provided
			final VODCondGen sm = getScopeManager();
			if (sm != null) {
				scope = ()-> sm.getGlobalScope();
				return true;
			}
			else throwTodoException("not-yet ready global scope");
		}
		return false;
	}
	
	@Override
	protected boolean equalsToCache(SystemElement e2) 
		throws ClassCastException, NullPointerException {
		return scope == ((ConditionElement) e2).scope;
	}
	
	public boolean equalsFunctionScope(ConditionElement ce2) {
		if (ce2 == null) return false;
		
		Function fs = getFunctionScope(), fs2 = ce2.getFunctionScope();
		return fs == null ? fs2 == null : fs.equalsFunction(fs2);
	}
	

	
//	/**
//	 * @return variable list for the hash-code polynomial.
//	 */
//	protected List<Integer> hashCodeVars() {
//		return Arrays.asList(scope == null || scope == this ? 0 : scope.hashCode());
//	}

	
	
//	public Boolean isConstantTo(Collection<Version<Variable>> vars) {
//		return isConstant();
//	}
	
	
	
	public <P extends Predicate> boolean independsOn(Collection<P> preds) {
		if (preds == null || preds.isEmpty()) throwNullArgumentException("predicate");

		@SuppressWarnings("rawtypes")
		final Set<Version> vrs = getNonConstVariableReferences(Version.class), 
				pvrs = new HashSet<>();
		for (P p : preds) pvrs.addAll(p.getProposition().getNonConstVariableReferences(Version.class));
		for (Version<?> vr : vrs) if (pvrs.contains(vr)) return false;
		for (Version<?> pvr : pvrs) if (vrs.contains(pvr)) return false;
		return true;
	}
	
	public boolean dependsOnOnly(Set<VariablePlaceholder<?>> vars) {
		if (vars == null || vars.isEmpty()) throwNullArgumentException("variable");
		
		return VariablePlaceholder
				.differVariables(getDirectVariablePlaceholders(), vars)
				.isEmpty();
	}
	
	/**
	 * @param pred
	 * @return true if both bounded and unbounded variables of two elements are the same.
	 */
	public boolean dependsOnTheSame(Predicate pred) {
		if (pred == null) throwNullArgumentException("predicate");

		return dependsOnTheSame(Arrays.asList(pred));
	}
	
	public <P extends Predicate> boolean dependsOnTheSame(Collection<P> preds) {
		if (preds == null || preds.isEmpty()) throwNullArgumentException("predicate");

		// the same bounded variables
		final Set<VariablePlaceholder<?>> qs = new HashSet<>();
		for (P p : preds) qs.addAll(p.getQuantifiers());
		if (dependsOnOnly(qs)) return true;
		
		// the same unbounded variables
		@SuppressWarnings("rawtypes")
		final Set<VariablePlaceholder> pvrs = new HashSet<>();
		for (P p : preds) 
			pvrs.addAll(p.getProposition().getNonConstVariableReferences(VariablePlaceholder.class));
		return VariablePlaceholder.differVariables(getNonConstVariableReferences(VariablePlaceholder.class), qs)
				.equals(VariablePlaceholder.differVariables(pvrs, qs));
	}

	
	/**
	 * Performing both keyword and symbol disambiguating.
	 * 
	 * @param format
	 * @param originalTerm - a keyword or symbol candidate
	 * @param disambiguousTerm - an ambiguous keyword or symbol candidate
	 * @return
	 */
	public String disambiguateString(SerialFormat format, 
			String originalTerm, String disambiguousTerm) {
		if (VODCondGen.isAmbiguous(this, originalTerm, format)) {
			if (disambiguousTerm == null) 
				throwTodoException("conflicting " + originalTerm);
			else if (VODCondGen.isAmbiguous(this, disambiguousTerm, format)) 
				throwTodoException("conflicting " + disambiguousTerm);
//			else disambiguousTerm = disambiguousTerm; 
		} else 
			disambiguousTerm = originalTerm; 
		
		return disambiguousTerm;
	}
	
	public String disambiguateZ3SmtString(
			String originalTerm, String disambiguousTerm) {
		return disambiguateString(SerialFormat.Z3_SMT, originalTerm, disambiguousTerm);
	}

	
	
	final public String toString() {
//		return tests(()-> isEmpty() && !isConstant())
		return guard(()-> 
			isSemanticallyEmpty() ? toEmptyString() : toNonEmptyString(false),
			()-> toString(leave("recursion", METHOD_TO_STRING)),
			e-> toString(leave(e.toString(), METHOD_TO_STRING)),
			METHOD_TO_STRING);
	}
	
	/**
	 * @return
	 */
	protected String toEmptyString() {
		return "(empty)";
	}

	/**
	 * TODO: For generating language-independent string description.
	 * 
	 * Default to generate Z3-SMT-compatible clauses now.
	 * 
	 * @param usesParenthesesAlready indicating enclosing the string by parentheses already or not.
	 * @return
	 */
	protected String toNonEmptyString(boolean usesParenthesesAlready) {
		return toString(SerialFormat.Z3_SMT);
	}

	private String toString(String cause) {
		return "(Not yet ready for " + super.toString() + " caused by " + cause + ")";
	}
	


	public String toString(SerialFormat format) {
		if (format == null) return toString();
		
		switch (format) {
		case Z3:	return toZ3String();
		case Z3_SMT:return toZ3SmtString(false, false, false);
		default:	// should NOT come here!
			assert(false); return null;
		}
	}

	public String toZ3String() {
		throwTodoException("supportting Z3 native format");
		return null;
	}
	
	public String toZ3SmtString(boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs) {
		String preCond = new String();
		if (printsVariableDeclaration || printsFunctionDefinition) 
			preCond += toZ3SmtDeclaration(VODCondGen.getPlatformConditions(SerialFormat.Z3_SMT));
		if (printsVariableDeclaration) 
			preCond += toZ3SmtVariableDeclaration();
		if (printsFunctionDefinition) {
//			preCond += (Function.toDefinitionString(SerialFormat.Z3_SMT) 
//					+ "\n");
			for (Function f : Function.sort(getFunctionReferences(null))) 
				preCond += toZ3SmtDeclaration(f.toZ3SmtString(printsVariableDeclaration, true, isLhs));
		}
		return preCond;
	}

	/**
	 * Excluding duplicate platform variable/function declaration.
	 * @param decl
	 * @return empty string if already declared
	 */
	public String toZ3SmtDeclaration(final String decl) {
		final VODCondGen cg = getCondGen();
		if (!cg.containsDeclaration(decl)) {
			cg.addDeclaration(decl);
			return "\n" + decl;
		}
		return "";
	}
	
	public String toZ3SmtVariableDeclaration() {
		String vd = new String();

		// declaring variable-derived intermediate pointers
		final Set<Pointer> usedPointers = getPointers();
		if (usedPointers != null && !usedPointers.isEmpty()) {
			vd += toZ3SmtDeclaration(PointerType.toZ3SmtString());
			
			// declaring prefix-expression pointer instances (*, **, etc) rather than types
//			final Set<Pointer> declaredPointers = new HashSet<>();
//			for (Pointer p : usedPointers) 	
//				/*
//				 * Z3-SMT pointer type is already declared by 
//				 * {@link #toDefinitionString(SerialFormat)}.
//				 * 
//				 *  Intermediate array access is natively supported by Z3
//				 */
//				declare: if (!(p instanceof Array) && p.isInstance()) {
//					for (Pointer dp : declaredPointers) 
//						if (p.equalsPointTo(dp)) break declare;
//					preCond += ("\n" + p.toZ3SmtString(true, false));
//					declaredPointers.add(p);
//				}
		}
		
		// declaring used variables, including ones used by pointers
		for (@SuppressWarnings("rawtypes") Version v : getVariableReferences()) 
			vd += toZ3SmtDeclaration(v.toZ3SmtString(true, false, false));
		return vd;
	}
	

	
	protected void throwCircularDependencyException(ConditionElement ce2, 
			ConditionElement dependingOn, StringBuffer dependingOnString) {
		throwTodoException(
				"Circular dependency b/w " + this + "\n\tand\n" + ce2 +
				" on " + dependingOn + " as " + dependingOnString);
	}
	
}