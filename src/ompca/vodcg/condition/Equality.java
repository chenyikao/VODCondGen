/**
 * 
 */
package ompca.vodcg.condition;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.NavigableSet;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTInitializerList;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import ompca.vodcg.ASTAddressable;
import ompca.vodcg.Assignable;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.data.Int;
import ompca.vodcg.condition.version.ConstArrayDeclaration;
import ompca.vodcg.condition.version.FunctionalVersion;
import ompca.vodcg.condition.version.VersionEnumerable;

/**
 * Equality	::= Expression ('=' Expression)+
 * 
 * @author Kao, Chen-yi
 *
 */
public class Equality extends OrderRelation 
implements AssignableExpression {

//	/**
//	 * Convenient (but hidden) constructor for a plain binary assignment, lhs = rhs.
//	 * 
//	 * @param lhs
//	 * @param rhs
//	 */
//	private Equality(Expression lhs, Expression rhs) {
//		// TODO: lhs.getScope() \/ rhs.getScope()
//		super(Operator.Equal, new HashSet<>(), lhs.getScopeManager());
//		
//		if (rhs == null) throwNullArgumentException("rhs. Empty or null operands are NOT allowed");
//		add(lhs, rhs);
//	}
	
	/**
	 * @param exps - may not be empty.
	 * @param scopeManager 
	 */
	private Equality(Set<Expression> exps, VODCondGen scopeManager) {
		super(Operator.Equal, exps, scopeManager);
	}

	/**
	 * @param exps - ordered list saving assigner information
	 * 	for an assignment side-effect
	 * @param scopeManager
	 */
	private Equality(List<Expression> exps, VODCondGen scopeManager) {
		super(Operator.Equal, exps, scopeManager);
	}
	
	

	/**
	 * Convenient constructor for a plain binary assignment, lhs = rhs.
	 * 
	 * @param lhs
	 * @param rhs
	 * @param condGen 
	 */
	static public Proposition from(IASTExpression lhs, IASTExpression rhs, final ASTAddressable rtAddr, VODCondGen condGen) {
//		this(Function.getFunctionScopeOf(lhs, condGen), condGen);
		return from(Expression.fromRecursively(lhs, rtAddr, condGen), 
					Expression.fromRecursively(rhs, rtAddr, condGen));
	}
	
	static public Proposition from(IASTEqualsInitializer init, final ASTAddressable rtAddr, VODCondGen condGen) {
		if (init == null) throwNullArgumentException("initializer");
		
//		this(Function.getFunctionScopeOf(init, condGen), condGen);
		try {
			final IASTInitializerClause ic = init.getInitializerClause();
			final Assignable<?> lhsAsn = Assignable.from((IASTDeclarator) init.getParent(), rtAddr, condGen);
			if (ic instanceof IASTInitializerList) {
				Proposition e = null;
				@SuppressWarnings("unchecked")
				final ConstArrayDeclaration lhs = (ConstArrayDeclaration) ConstArrayDeclaration.from((Assignable<PathVariable>) lhsAsn);
				int i = 0;
				for (IASTInitializerClause lic : ((IASTInitializerList) ic).getClauses()) {
					final Expression rhs = Expression.fromRecursively(lic, rtAddr, condGen);
					final Equality eq = fromAssignment(lhs.getAssigned(i++, rhs), rhs);
					e = e == null ? eq : e.and(eq);
				}
				return e;
				
			} else return fromAssignment(
					PathVariablePlaceholder.from(lhsAsn), Expression.fromRecursively(ic, rtAddr, condGen));
		
		} catch (Exception e) {
			return throwTodoException(e);
		}
		
//		IASTExpression asgOprd = asg.getOperand();
//		Expression operand = Expression.from(asgOprd, sideEffect);
//		if (operand instanceof PathVariable) 
//			((PathVariable) operand).reversion(LValue.from(asgOprd), scope);
	}
	
//	public static Proposition from(ArithmeticExpression lhs, ArithmeticExpression rhs) {
//		if (lhs == null) throwNullArgumentException("lhs");
//		if (rhs == null) throwNullArgumentException("rhs");
//		return from(lhs.toExpression(), rhs.toExpression());
//	}
	
	public static Proposition from(Expression lhs, Expression rhs) {
		return from(Operator.Equal, lhs, rhs, ()-> 
		new Equality(Arrays.asList(lhs, rhs), lhs.getCondGen()));
	}
	
	public static Proposition from(Collection<? extends Expression> operands) {
		Proposition eq = from(Operator.Equal, operands);
		if (eq != null && !eq.getOp().equals(Operator.Equal)) return eq;
		
		assert operands.size() > 1;
		final Iterator<? extends Expression> oit = operands.iterator();
		eq = from(oit.next(), oit.next());
		while (oit.hasNext()) eq = from(eq, oit.next());
		return eq;
	}
	
	/**
	 * Factory constructor for an AST-derived unary assignment.
	 * @param expOp - Op code of {@link IASTUnaryExpression}
	 * @param pvp
	 * @return
	 */
	public static Proposition from(int expOp, PathVariablePlaceholder pvp) {
		if (pvp == null) throwNullArgumentException("delegate"); 
		if (pvp.isDirectlyFunctional()) switch (expOp) {
			// Subtraction assignment: clause--, --clause
			case IASTUnaryExpression.op_postFixDecr	: 
			case IASTUnaryExpression.op_prefixDecr	: 
				return fromFunctional(IASTBinaryExpression.op_minusAssign, pvp, Int.ONE);
				
				// Addition assignment: clause++, ++clause
			case IASTUnaryExpression.op_postFixIncr	: 
			case IASTUnaryExpression.op_prefixIncr	: 
				return fromFunctional(IASTBinaryExpression.op_plusAssign, pvp, Int.ONE);
		}
		if (pvp.isLoopIterator()) return ExpressionRange.fromIteratorOf(
				pvp.getEnclosingCanonicalLoop(), pvp.cacheRuntimeAddress(), pvp.getCondGen());

		// constant counting non-functional variable versions
		final NavigableSet<PathVariablePlaceholder> prs = pvp.previousRuntimes();
		if (prs.isEmpty()) throwTodoException("not initialized placeholder");
		if (prs.size() != 1) throwTodoException("unsupported conditional placeholders");
//		Elemental.consumeNonNull(nv-> ppvd.reversion(nv), ()-> pvd.getVersion().appendConstantCounting());
		
		Proposition asm = null;
		final PathVariablePlaceholder ppvp = prs.first();
		switch (expOp) {
		// Subtraction assignment: clause--, --clause
		case IASTUnaryExpression.op_postFixDecr	: 
		case IASTUnaryExpression.op_prefixDecr	: 
			asm = fromAssignment(pvp, (Expression) ppvp.subtract(Int.ONE));
			break;

		// Addition assignment: clause++, ++clause
		case IASTUnaryExpression.op_postFixIncr	: 
		case IASTUnaryExpression.op_prefixIncr	: 
			asm = fromAssignment(pvp, (Expression) ppvp.add(Int.ONE));
		}
		
		if (asm == null) throwTodoException("unsupported assignment");
//		if (asm instanceof Equality) ((Equality) asm).setAssigned();
		return asm;
	}
	
	/**
	 * Factory constructor for an AST-derived binary assignment.
	 * 
	 * @param expOp - Op code of {@link IASTBinaryExpression}
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	public static Proposition from(int expOp, Expression lhs, final Expression rhs) {
		if (lhs == null) throwNullArgumentException("lhs");
		if (rhs == null) throwNullArgumentException("rhs");
		
		Proposition eq = null;
		switch (expOp) {
		// ==: non-assignment-equality binary relational proposition
		case IASTBinaryExpression.op_equals:
			eq = from(lhs, rhs);
			break;
		// =: a ::= a makes no side-effects, even tautology
		case IASTBinaryExpression.op_assign:
			if (lhs != rhs) {
				eq = fromAssignment(lhs, rhs);
//				eq = new Equality(Arrays.asList(lhs, rhs), ()-> rhs.getCondGen());
//				((Equality) eq).setAssigned();
			}
			break;
		}
		return eq != null ? eq : fromFunctional(expOp, lhs, rhs);
	}
		
	public static Proposition from(OrderRelation or) {
		if (or == null) return null;
		if (or instanceof Equality) return (Equality) or;
		if (or.getOp() == Operator.Equal) return from(or.getOperands());
		return null;
	}
	
	private static Equality fromAssignment(Expression lhs, Expression rhs) {
		final Proposition p = from(lhs, rhs);
		if (lhs instanceof AssignableExpression) 
			((AssignableExpression) lhs).setAssigned(rhs);
		if (p instanceof Equality) {
			final Equality eq = (Equality) p;
//			eq.setAssigned();
			return eq;
		}
		return throwTodoException("unsupported assignment");
	}
	
	/**
	 * @param expOp
	 * @param lhs
	 * @param rhs
	 * @return TODO? boolean functional closure trinity:
	 * 	expanding loop iteration equality for constant/non-constant-mixed i: i1=i0+/-1, i2=i1+/-1,...
	 * 	<code><pre>
	 * 	final Proposition prop = pvd.isFunctional()
	 * 		? FunctionalIntInputVersion.from(pvd.getAssignable()).getFuncCallView().toProposition()
	 * 		: Equality.from(unaryOp, pvd);
	 */
	@SuppressWarnings("unchecked")
	private static Proposition fromFunctional(int expOp, Expression lhs, final Expression rhs) {
		assert lhs != null && rhs != null;
		try {
		Expression plhs = null;
		if (lhs instanceof AssignableExpression) {
			final Assignable<?> lhsAsn = ((AssignableExpression) lhs).getAssignable();
			if (lhsAsn.hasDependingLoop()) {
				// Handling sequential loop-dependent self assignments only
				lhs = FunctionalVersion.from((Assignable<PathVariable>) lhsAsn); 
				plhs = ((FunctionalVersion) lhs).cloneAssigner();
			}
		}
		if (plhs == null) {
			if (lhs instanceof VersionEnumerable) 
				plhs = (Expression) ((VersionEnumerable<?>) lhs).previousRuntimeAssigneds();
			else if (plhs instanceof PathVariablePlaceholder) {
				final PathVariablePlaceholder pvp = (PathVariablePlaceholder) plhs;
				if (pvp.isLoopIterator()) return ExpressionRange.fromIteratorOf(
						pvp.getEnclosingCanonicalLoop(), pvp.cacheRuntimeAddress(), pvp.getCondGen());
			}
		}
		if (plhs == null) throwTodoException("unsupported equality");

		switch (expOp) {
		// /=
		case IASTBinaryExpression.op_divideAssign:
			// TODO: new Arithmetic(Arithmetic.Operator.IntegerDivide, ...);
			return fromAssignment(lhs, Arithmetic.from(Arithmetic.Operator.Divide, plhs, rhs));
		// -=
		case IASTBinaryExpression.op_minusAssign:
			return fromAssignment(lhs, Arithmetic.from(Arithmetic.Operator.Subtract, plhs, rhs));
		// %=
		case IASTBinaryExpression.op_moduloAssign:
			return fromAssignment(lhs, Arithmetic.from(Arithmetic.Operator.Modulo, plhs, rhs));
		// *=
		case IASTBinaryExpression.op_multiplyAssign:
			return fromAssignment(lhs, Arithmetic.from(Arithmetic.Operator.Multiply, plhs, rhs));
		// +=
		case IASTBinaryExpression.op_plusAssign:
			return fromAssignment(lhs, Arithmetic.from(Arithmetic.Operator.Add, plhs, rhs));
		// TODO: &=?
		case IASTBinaryExpression.op_binaryAndAssign:
		// TODO: |=?
		case IASTBinaryExpression.op_binaryOrAssign:
		// TODO: ^=?
		case IASTBinaryExpression.op_binaryXorAssign:
		// TODO: <<=?
		case IASTBinaryExpression.op_shiftLeftAssign:
		// TODO: >>=?
		case IASTBinaryExpression.op_shiftRightAssign:
		}} catch (Exception e) {
//		}} catch (ClassCastException | NoSuchVersionException e) {
			return throwTodoException(e);
		}
		
//		if (eq instanceof Equality) ((Equality) eq).setAssigned();
		return throwTodoException("unsupported equality");
	}
	
	
	
	protected Proposition andByReduce(Proposition p2) {
		if (p2 == null) throwNullArgumentException("p2");
		
		Proposition result = null;
		if (p2 instanceof Equality) 
			result = andByReduce((Equality) p2);
		
		else if (p2 instanceof OrderRelation) {
			Proposition eq = Equality.from((OrderRelation) p2);
			if (eq != null) result = andByReduce(eq);
		}
		return result;
	}
	
	@SuppressWarnings("unchecked")
	private Proposition andByReduce(Equality eq2) {
		if (isEmpty()) return eq2;
		
		boolean equalsE2 = false;
		final Set<Expression> exps1 = new HashSet<>(getOperands());
		final Collection<Expression> exps2 = (Collection<Expression>) eq2.getOperands();
		for (Expression exp2 : exps2) 
			if (equalsE2 |= contains(exp2)) break;
		if (equalsE2) {
			for (Expression exp2 : exps2) 
				for (Expression exp1 : exps1) 
					if (exp1 instanceof ArithmeticExpression 
							&& exp2 instanceof ArithmeticExpression) {
						final ArithmeticExpression ae1 = (ArithmeticExpression) exp1,
								ae2 = (ArithmeticExpression) exp2;
						final Proposition equalAe2 = ae1.equal(ae2);
						if (equalAe2.isFalse()) return equalAe2;	// Contradiction!
					}
			exps1.addAll(exps2);
			return new Equality(exps1, getCondGen());
		}

		return null;
	}

//	protected Proposition andNonConst(Predicate pred) {
//		// for each exp E, if any var V of E is one of the quantifiers Q, then we have E /\ P = TODO 
//		pred.getQuantifiers();
//		if (pred instanceof Equality) {
//			List<Expression> exp2s = ((Equality) pred).getExpressions();
//			if (operands.isEmpty()) {operands.addAll(exp2s); return this;}
//			else for (Expression exp1 : operands) for (Expression exp2 : exp2s) if (exp1.equals(exp2)) {
//				operands.addAll(exp2s); return this;
//			}
//		}
//		return FALSE;
//	}

	
	
//	/**
//	 * @see ompca.condition.OrderRelation#notByReduce()
//	 */
//	protected Proposition notByReduce() {
//			And eq = new And(getScopeManager());
//			Expression[] eqArray = exps.toArray(new Expression[]{});
//			for (int i = 0; i < eqArray.length - 1; i++) try {
//				eq.and(new Equality(eqArray[i], eqArray[i+1], null));
//			} catch (CoreException | InterruptedException e) {
//				e.printStackTrace();
//			}
//			return eq.not();
//	}
	
	

	@Override
	public Expression getAssignerIf() {
		return isBinary() 
				? getRightHandSide()
				: throwTodoException("unsupported equality");
	}
	
//	@Override
//	public Boolean isAssigned() {
//		Boolean isA = AssignableExpression.super.isAssigned();
//		if (isA == null) {
//			isA = getAssigned() != null;
//			setAssigned(isA);
//		}
//		return isA;
//	}
	
	@Override
	public Assignable<?> getAssignable() {
		if (isBinary()) {
			Expression lhs = getLeftHandSide();
			while (lhs != null) {
				if (lhs instanceof AssignableExpression) return ((AssignableExpression) lhs).getAssignable();
				if (lhs instanceof Relation) lhs = ((Relation) lhs).getLeftHandSide();
				else break;
			}
		}
		return throwTodoException("unsupported assignment");
	}
	
	public Expression getAssigned() {
		if (tests(isAssigned())) {
			return isBinary() 
					? getLeftHandSide() 
					: throwTodoException("unsupported assignment");
			// inconsistent assigners since clone-reversion
//			for(Expression oprd : getOperands())
		}
		return null;
	}
	
	@Override
	public Boolean isAssigned() {
//		if (hasAssignable()) return AssignableExpression.super.isAssigned();

		final Expression lhs = getLeftHandSide();
		if (lhs == null) return null;
		if (lhs instanceof AssignableExpression) return ((AssignableExpression) lhs).isAssigned();
		return throwTodoException("unsupported lhs");
	}

	@Override
	public void setAssigned(Boolean isAssigned) {
		Expression lhs = getLeftHandSide();
		while (true) {
			if (lhs == null) throwNullArgumentException("lhs");
			else if (lhs instanceof AssignableExpression) {
				((AssignableExpression) lhs).setAssigned(isAssigned);
				break;
			}
			else if (lhs instanceof Relation) lhs = ((Relation) lhs).getLeftHandSide();
		}
	}
	
//	@Override
//	public void setAssigned(Expression lhs, Expression rhs) {
//		setAssigned();	// for the parent assignment expression
//		if (lhs == null) throwNullArgumentException("lhs");
//		lhs.setAssigned(rhs, getAssignment());
//	}
	
	
	
	/**
	 * @see ompca.condition.OrderRelation#toConstant()
	 */
	protected Expression toConstantIf() {
//		return get(toConstantOperands());
		return this;
	}
	
	
	
	/**
	 * TODO: reusing {@link Proposition#toZ3SmtString(boolean, boolean, boolean)} to handle locals.
	 * 
	 * @see ompca.condition.Proposition#toZ3SmtString(boolean, boolean, boolean)
	 */
	public java.lang.String toZ3SmtString(
			boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs) {
		final Expression asd = getAssigned();
		return asd != null && asd.isZ3ArrayAccess() 
				? asd.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition, true)
				: super.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition, isLhs);
	}

}