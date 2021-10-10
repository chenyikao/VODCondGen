/**
 * 
 */
package ompca.vodcg.condition;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

import org.eclipse.cdt.core.dom.IName;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IBinding;
import org.eclipse.cdt.core.dom.ast.IVariable;

import ompca.condition.SerialFormat;
import ompca.vodcg.ASTAddressable;
import ompca.vodcg.ASTUtil;
import ompca.vodcg.Assignable;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.data.ArithmeticGuard;
import ompca.vodcg.condition.data.DataType;
import ompca.vodcg.condition.data.PlatformType;
import ompca.vodcg.condition.version.FunctionallableRole;
import ompca.vodcg.condition.version.ThreadRole;
import ompca.vodcg.condition.version.Version;

/**
 * @author Kao, Chen-yi
 *
 */
public class Variable extends Referenceable {

//	private static final Method METHOD_FROM_NON_AST = 
//			Elemental.getMethod(Variable.class, "fromNonAST", String.class, PlatformType.class, boolean.class, Supplier.class, IASTStatement.class, Supplier.class);

	/**
	 * Even a non-AST variable may still bind to some AST structure.
	 */
	private IASTStatement astScope = null;
	private Boolean isParam = null;
	
	/**
	 * Non AST variables include the API/library parameters (i.e., boundary path variables)
	 */
	private static final Map<String, Set<Variable>> NON_AST_VARIABLES = 
			new HashMap<>();
	
	/**
	 * Constructor for a non-AST variable.
	 * 
	 * @param name
	 * @param type
	 * @param isParameter - true if it's a non-AST function parameter
	 * @param astScope
	 * @param condGen
	 */
	private Variable(String name, PlatformType type, boolean isParameter,
			IASTStatement astScope, VODCondGen condGen) {
		super(name, type, condGen);
		this.astScope = astScope;
		this.isParam = isParameter;
	}
	
	protected Variable(IName name, PlatformType type, final ASTAddressable rtAddr, VODCondGen condGen) {
		super(name, type, rtAddr, condGen);
	}
	
	protected Variable(IName name, final ASTAddressable rtAddr, VODCondGen condGen) {
		this(name, (PlatformType) null, rtAddr, condGen);
	}
	
//	protected Variable(IASTName name, DataType type) 
//			throws IllegalArgumentException, CoreException, InterruptedException {
//		this(name, type, Function.getScopeOf(name));
//	}
	
	protected Variable(IASTName name, IBinding bind, final ASTAddressable rtAddr, VODCondGen condGen) {
		super(name, bind, rtAddr, condGen);
	}
	
	public static Variable fromNonAST(String name, PlatformType type, boolean isParameter,
			Supplier<? extends ConditionElement> scope, IASTStatement astScope, VODCondGen condGen) {
		if (scope == null) throwNullArgumentException("scope");

		Set<Variable> vars = NON_AST_VARIABLES.get(name);
		if (vars == null) NON_AST_VARIABLES.put(name, vars = new HashSet<>()); 
		else for (Variable v : vars) 
			if (guardTests(()-> v.getScope() == scope.get())) return v;
			
		final Variable v = new Variable(name, type, isParameter, astScope, condGen);
		// setScope() -> isGlobal() -> funcScope
		v.setScope(scope);
		vars.add(v);	// hashCode depends on funcScope
		return v;
	}

	public static Variable fromNonAST(IVariable var, boolean isParameter,
			Supplier<ConditionElement> scope, IASTStatement astScope, VODCondGen condGen) {
		if (var == null) throwNullArgumentException("AST variable");

		return fromNonAST(var.getName(),
				DataType.from(var.getType()), 
				isParameter, scope, astScope, condGen);
	}

	

	/**
	 * @return
	 * @see #astScope
	 */
	public IASTStatement getASTScope() {
		return astScope;
	}
	
	@Override
	public String getIDSuffix(final SerialFormat format) {
		return debugGetNonNull(()-> isParameter()
				? getFunctionScope().getName()
				: getScope().getIDSuffix(format));
	}
	
	@Override
	public FunctionallableRole getThreadRole() {
		return get(()-> super.getThreadRole(),
				()-> isThreadPrivate() ? ThreadRole.NON_MASTER : ThreadRole.MASTER);
//		return throwUnsupportedRoleException();
	}

	
	
	/**
	 * A variable declaration has no references (instances) for now.
	 * TODO: return ALL path and non-path references to this variable.
	 * 
	 * @see ompca.condition.ConditionElement#getDirectVariableReferences()
	 */
	@Override
	protected <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType) {
		return null;
	}
	
	@Override
	protected Set<ArithmeticGuard> cacheArithmeticGuards() {
		return null;
	}
	
	@Override
	protected Set<Function> cacheDirectFunctionReferences() {
		return null;
	}
	
	/**
	 * A variable declaration has no side effects for now.
	 * TODO: return ALL delegate side effects of this variable.
	 * 
	 * @see ompca.condition.Expression#cacheDirectSideEffect()
	 */
	@Override
	protected void cacheDirectSideEffect() {
	}
	

	
//	/**
//	 * @param lowerBound
//	 * @param upperBound
//	 * @return
//	 */
//	public VariableRange getRangeOf(Expression lowerBound, Expression upperBound) {
//		return VariableRange.get(this, lowerBound, upperBound);
//	}


	
	/**
	 * @param vars1
	 * @param vars2
	 * @return
	 */
	public static boolean conflictsByName(Collection<Version<Variable>> vars1,
			Collection<VariablePlaceholder<?>> vars2) {
		for (Version<Variable> v1 : vars1)
			for (VariablePlaceholder<?> v2d : vars2) {
				@SuppressWarnings("unchecked")
				Version<Variable> v2 = (Version<Variable>) v2d.getSubject();
				if (v1.equalsId(v2, null) && !v1.equals(v2)) return true;
			}
		return false;
	}

	/* (non-Javadoc)
	 * @see ompca.condition.Expression#containsArithmetic()
	 */
	@Override
	public boolean containsArithmetic() {
		return false;
	}
	

	
	public boolean isParameter() {
		if (isParam != null) return isParam;
		
		final IASTName cName = getASTName();
		if (cName != null) {
			final Assignable<?> def = Assignable.from(
					ASTUtil.getDefinitionOf(cName), true, getCondGen());
			if (def != null) return isParam = def.isParameter();
		}
		
		return isParam;
	}

	
	
	@Override
	protected List<Integer> hashCodeVars() {
		final List<Integer> hcvs = new ArrayList<>(super.hashCodeVars());
		hcvs.add(get(()-> astScope.hashCode(), ()-> 0)); 
		hcvs.add(get(()-> isParam.hashCode(), ()-> 0));
//		hcvs.add(get(()-> getFunctionScope().hashCode(), ()-> 0));
		return hcvs;
	}

	
	
	/**
	 * TODO: A variable (not reference) negation means ALL possible references to it SHOULD be negated.
	 * 
	 * @see ompca.condition.Expression#negate()
	 */
	@Override
	public Expression negate() {
		return null;
	}

	
	
	@Override
	public void setFunctionScope(Supplier<Function> scope) {
		if (scope == null && isParameter()) 
			throwInvalidityException("non-global parameter");
		super.setFunctionScope(scope);
	}

	
	
	protected String toNonEmptyString(boolean usesParenAlready) {
		return getName();
	}
	
	/** 
	 * For parameter declaration.
	 * @see ompca.condition.Referenceable#toZ3SmtString(boolean, boolean, boolean)
	 */
	@Override
	public String toZ3SmtString(boolean printsVariableDeclaration, 
			boolean printsFunctionDefinition, boolean isLhs) {
		final String id = super.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition, isLhs);
		if (printsFunctionDefinition) return 
				"(" + id + " " + 
				getType().toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition) +
				")";
		return id;
	}

}