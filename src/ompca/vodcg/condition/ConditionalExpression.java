/**
 * 
 */
package ompca.vodcg.condition;

import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;

import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.Elemental;
import ompca.vodcg.ASTException;
import ompca.vodcg.SystemElement;
import ompca.vodcg.UncertainException;
import ompca.vodcg.condition.data.ArithmeticGuard;
import ompca.vodcg.condition.data.PlatformType;
import ompca.vodcg.condition.data.Pointer;
import ompca.vodcg.condition.version.FunctionallableRole;
import ompca.vodcg.condition.version.ThreadRoleMatchable;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class ConditionalExpression 
extends Expression implements ArithmeticExpression {

	static private final Method METHOD_REDUCE_ONCE = 
			Elemental.getMethod(ConditionalExpression.class, "reduceOnce");

	
	
	private Proposition cond = null;
	private Expression trueExp = null;
	private Expression falseExp = null;
	
	private ConditionalExpression(Proposition cond, Expression te, Expression fe) {
		super(cond.cacheRuntimeAddress(), cond.getScopeManager());
		assert cond != null && te != null && fe != null;
		
		this.cond = cond;
		trueExp = te;
		falseExp = fe;
	}
	
	/** <pre>
	 * Case (cond ? y : z)		= (cond && y) || (!cond && z) 
	 * Case (cond ? true : y)	= (cond && true) || (!cond && y)	= cond || (!cond && y)
	 * Case (cond ? false : y)	= (cond && false) || (!cond && y)	= !cond && y
	 * Case (cond ? y : true)	= (cond && y) || (!cond && true)	= (cond && y) || !cond
	 * Case (cond ? y : false)	= (cond && y) || (!cond && false)	= cond && y
	 * </pre>
	 *
	 * @param cond
	 * @param trueExp
	 * @param falseExp
	 * @return
	 */
	final public static Expression from(Proposition cond, 
			Expression trueExp, Expression falseExp) {
		if (cond == null) throwNullArgumentException("condition");
		if (trueExp == null) throwNullArgumentException("true expression");
		if (falseExp == null) throwNullArgumentException("false expression");

		if (cond.isTrue() || trueExp.equals(falseExp)) return trueExp;	// cond.reduce();
		if (cond.isFalse()) return falseExp;

		if (trueExp instanceof Proposition) {
			final Proposition trueProp = (Proposition) trueExp;
			final Supplier<Proposition> falseSup = ()-> cond.not().and(()-> falseExp.toProposition());

			// Case (cond ? true : y)	= cond || (!cond && y)
			if (trueProp.isTrue()) return cond.or(falseSup);
			// Case (cond ? false : y)	= !cond && y
			if (trueProp.isFalse()) return falseSup.get();
		}
		if (falseExp instanceof Proposition) {
			final Proposition falseProp = (Proposition) falseExp;
			final Supplier<Proposition> trueSup = ()-> cond.and(()-> trueExp.toProposition());
			
			// Case (cond ? y : true)	= (cond && y) || !cond
			if (falseProp.isTrue()) return cond.not().or(trueSup);
			// Case (cond ? y : false)	= cond && y
			if (falseProp.isFalse()) return trueSup.get();
		}
		return new ConditionalExpression(cond, trueExp, falseExp);
	}

	
	
	/**
	 * lazy scope setting:
	 * cond.scope \/ trueExp.scope \/ falseExp.scope
	 */
	@Override
	protected ConditionElement cacheScope() {
		assert cond != null && trueExp != null && falseExp != null;
		try {
			return getSkipNull(()-> 
			cond.getCommonScope(trueExp).getCommonScope(falseExp));
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}

	@Override
	protected Set<ArithmeticGuard> cacheArithmeticGuards() {
		Set<ArithmeticGuard> ags = new HashSet<>();
		ags.addAll(cond.getArithmeticGuards());
		ags.addAll(trueExp.getArithmeticGuards());
		ags.addAll(falseExp.getArithmeticGuards());
		return ags;
	}
	
	@Override
	protected Boolean cacheConstant() {
		return cond.isConstant();
	}
	
	@Override
	protected Boolean cacheGlobal() {
		return cond.isGlobal();
	}

	@Override
	protected Set<Function> cacheDirectFunctionReferences() {
		Set<Function> condRefs = cond == null ? null : cond.getDirectFunctionReferences(),
				tRefs = trueExp == null ? null : trueExp.getDirectFunctionReferences(),
						fRefs = falseExp == null ? null : falseExp.getDirectFunctionReferences();
		
		if (condRefs == null) 
			condRefs = tRefs != null ? tRefs : fRefs; 
		else {
			if (tRefs != null && condRefs != tRefs) condRefs.addAll(tRefs);
			if (fRefs != null && condRefs != fRefs) condRefs.addAll(fRefs);
		}
		return condRefs;
	}
	
	/* (non-Javadoc)
	 * @see ompca.condition.ConditionElement#getVariableReferences()
	 */
	@Override
	protected <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType) {
		final Set<T> vrs = new HashSet<>();
		if (cond != null) vrs.addAll(cond.getDirectVariableReferences(refType));
		if (trueExp != null) vrs.addAll(trueExp.getDirectVariableReferences(refType));
		if (falseExp != null) vrs.addAll(falseExp.getDirectVariableReferences(refType));
		return vrs;
	}
	
	@Override
	protected void cacheDirectSideEffect() {
		andSideEffect(()-> cond.getSideEffect());
		// trueExp.getSideEffect() and falseExp.getSideEffect() may be conflict to each other
//		andSideEffect(()-> trueExp.getSideEffect());
//		andSideEffect(()-> falseExp.getSideEffect());
	}



	public Proposition getCondition() {
		return cond;
	}

	public Expression getTrueExpression() {
		return trueExp;
	}
	
	public Expression getFalseExpression() {
		return falseExp;
	}
	
	/**
	 * @return Condition's privatizing block. 
	 * 	While trueExp's or falseExp's are foreign private.
	 */
	@Override
	public IASTStatement getPrivatizingBlock() {
		assert cond != null;
		return cond.getPrivatizingBlock();
	}
	
	@Override
	public FunctionallableRole getThreadRole() {
		return get(()-> super.getThreadRole(),
				()-> ThreadRoleMatchable.getThreadRole(cond, trueExp, falseExp));
	}
	
	/**
	 * TODO: type-checking
	 * 
	 * @see ompca.condition.Expression#getType()
	 */
	@Override
	public PlatformType getType() {
//		return DataType.get(trueExp.getType(), falseExp.getType());
//		if (cond.equals(Proposition.TRUE)) return trueExp.getType();
		if (cond.isFalse()) return falseExp.getType();
		return trueExp.getType();
	}
	
	/* (non-Javadoc)
	 * @see ompca.condition.ConditionElement#getPointers()
	 */
	@Override
	public Set<Pointer> getPointers() {
		Set<Pointer> ps = new HashSet<>();
		if (cond != null) ps.addAll(cond.getPointers());
		if (trueExp != null) ps.addAll(trueExp.getPointers());
		if (falseExp != null) ps.addAll(falseExp.getPointers());
		return ps;
	}
	
	

	/* (non-Javadoc)
	 * @see ompca.condition.ConditionElement#isEmpty()
	 */
	@Override
	public boolean isEmpty() {
		return cond == null;
	}

	@Override
	public Boolean isZero() {
		try {
			// conjunctive fast checking
			return ((ArithmeticExpression) trueExp).isZero()
					&& ((ArithmeticExpression) falseExp).isZero();
			
		} catch (NullPointerException | ClassCastException e) {
			return null;
		}
	}
	
	@Override
	public Boolean isPositive() {
		try {
			// conjunctive fast checking
			return ((ArithmeticExpression) trueExp).isPositive()
					&& ((ArithmeticExpression) falseExp).isPositive();
		
		} catch (NullPointerException | ClassCastException e) {
			return null;
		}
	}
	
	@Override
	public Boolean isPositiveInfinity() {
		try {
			// conjunctive fast checking
			return ((ArithmeticExpression) trueExp).isPositiveInfinity()
					&& ((ArithmeticExpression) falseExp).isPositiveInfinity();
			
		} catch (NullPointerException | ClassCastException e) {
			return null;
		}
	}
	
	@Override
	public Boolean isNegative() {
		try {
			// conjunctive fast checking
			return ((ArithmeticExpression) trueExp).isNegative()
					&& ((ArithmeticExpression) falseExp).isNegative();
		} catch (NullPointerException | ClassCastException e) {
			return null;
		}
	}

	@Override
	public Boolean isNegativeInfinity() {
		try {
			// conjunctive fast checking
			return ((ArithmeticExpression) trueExp).isNegativeInfinity()
					&& ((ArithmeticExpression) falseExp).isNegativeInfinity();
		} catch (NullPointerException | ClassCastException e) {
			return null;
		}
	}
	
	
	
//	private final static Method METHOD_EXPRESSION_TRAVERSAL = 
//			getMethod(ConditionalExpression.class, "initiatesExpressionTraversal");
//	/* (non-Javadoc)
//	 * @see ompca.condition.ArithmeticExpression#initiatesExpressionTraversal()
//	 */
//	@Override
//	public boolean initiatesExpressionComputation() {
//		return initiatesElementalTraversal(METHOD_EXPRESSION_TRAVERSAL);
//	}
//
//	/* (non-Javadoc)
//	 * @see ompca.condition.ArithmeticExpression#initiateExpressionTraversal()
//	 */
//	@Override
//	public void initiateExpressionComputation() {
//		initiateElementalTraversal(METHOD_EXPRESSION_TRAVERSAL);
//	}
//
//	/* (non-Javadoc)
//	 * @see ompca.condition.ArithmeticExpression#resetExpressionTraversal()
//	 */
//	@Override
//	public void resetExpressionComputation() {
//		resetElementalTraversal(METHOD_EXPRESSION_TRAVERSAL);
//	}
	
	
	
	/* (non-Javadoc)
	 * @see ompca.condition.Expression#containsArithmetic()
	 */
	@Override
	public boolean containsArithmetic() {
		Boolean test = Elemental.testsAnySkipNullException( 
				()-> cond.containsArithmetic(),
				()-> trueExp.containsArithmetic(),
				()-> falseExp.containsArithmetic());
		return test != null && test;
	}

	

	@Override
	public Boolean dependsOn(Expression v) {
		try {
			return Elemental.testsAnySkipNull(()-> cond.dependsOn(v),
					()-> trueExp.dependsOn(v),
					()-> falseExp.dependsOn(v));
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	

	
	protected boolean equalsToCache(SystemElement e2) {
		ConditionalExpression ce2 = (ConditionalExpression) e2;
		Proposition cond2 = ce2.cond;
		Expression te2 = ce2.trueExp, fe2 = ce2.falseExp;
		return (cond == null ? cond2 == null : cond.equals(cond2)) 
				&& (trueExp == null ? te2 == null : trueExp.equals(te2))
				&& (falseExp == null ? fe2 == null : falseExp.equals(fe2));
	}
	
	protected List<Integer> hashCodeVars() {
		assert cond != null && trueExp != null && falseExp != null;
		return Arrays.asList(cond.hashCode(), trueExp.hashCode(), falseExp.hashCode());
	}

	
	/**
	 * TODO: negate().toProposition().equals(toProposition().not())?
	 * @see ompca.condition.Expression#negate()
	 */
	@Override
	public Expression negate() {
//		return from(cond, falseExp, trueExp);
		return from((Proposition) cond.negate(), trueExp, falseExp);
	}
	
	
	
	@SuppressWarnings("unchecked")
	protected ConditionalExpression reduceOnce() {
		assert cond != null && trueExp != null && falseExp != null;
		cond = cond.reduce(METHOD_REDUCE_ONCE);
		trueExp = (Expression) trueExp.reduce(METHOD_REDUCE_ONCE);
		falseExp = (Expression) falseExp.reduce(METHOD_REDUCE_ONCE);
		
		super.reduceOnce();
		return this;
	}

	
	
	@SuppressWarnings("unchecked")
	protected Expression toConstantIf() 
		throws ASTException, UncertainException {
		assert cond != null && trueExp != null && falseExp != null;
		final Proposition cc = (Proposition) cond.toConstantIf();
		if (cc.isTrue()) return trueExp;
		if (cc.isFalse()) return falseExp;
		return throwTodoException("non-reduced constant conditional expression");
	}

	/**
	 * Propositional side-effect of ConditionalExpression
	 * = (cond /\ (Proposition) trueExp) \/ (~cond /\ (Proposition) falseExp)
	 * 
	 * @see ompca.condition.Expression#toProposition()
	 */
	public Proposition toProposition() {
		if ((trueExp instanceof Proposition 
				|| trueExp instanceof ConditionalExpression) 
				&& (falseExp instanceof Proposition 
						|| falseExp instanceof ConditionalExpression))
			andSideEffect(()-> 
			cond.and(()-> trueExp.toProposition()).or(()->
			cond.not().and(()-> falseExp.toProposition())));
		return super.toProposition();
	}
	
	
	
	protected String toNonEmptyString(boolean usesParenthesesAlready) {
		return ((usesParenthesesAlready) ? "" : "(") 
				+ cond.toNonEmptyString(true) + ")?(" 
				+ trueExp.toNonEmptyString(true) + "):(" 
				+ falseExp.toNonEmptyString(true) 
				+ ((usesParenthesesAlready) ? "" : ")");
	}
	

	
	/* (non-Javadoc)
	 * @see ompca.condition.ConditionElement#toZ3SmtString()
	 */
	@Override
	public String toZ3SmtString(boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs) {
		return "(ite " + cond.toZ3SmtString(false, false, isLhs) + 
				" " + trueExp.toZ3SmtString(false, false, isLhs) + 
				" " + falseExp.toZ3SmtString(false, false, isLhs) + ")";
	}

}