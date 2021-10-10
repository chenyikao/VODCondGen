/**
 * 
 */
package ompca.vodcg.condition;

import java.util.Collection;
import java.util.Set;
import java.util.function.Supplier;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import ompca.DebugElement;
import ompca.Elemental;
import ompca.vodcg.ASTAddressable;
import ompca.vodcg.ASTException;
import ompca.vodcg.ASTLoopUtil;
import ompca.vodcg.ASTUtil;
import ompca.vodcg.Assignable;
import ompca.vodcg.ReenterException;
import ompca.vodcg.SystemElement;
import ompca.vodcg.UncertainException;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.Arithmetic.Operator;
import ompca.vodcg.condition.data.Int;
import ompca.vodcg.condition.data.Number;
import ompca.vodcg.condition.data.NumericExpression;
import ompca.vodcg.condition.version.FunctionallableRole;
import ompca.vodcg.condition.version.ThreadRoleMatchable;
import ompca.vodcg.condition.version.Version;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public interface ArithmeticExpression extends NumericExpression, ThreadRoleMatchable {

	static public ArithmeticExpression from(
			Operator op, ArithmeticExpression lhs, ArithmeticExpression rhs) 
			throws ASTException, ReenterException {
		if (op == null) DebugElement.throwNullArgumentException("operator");
		if (lhs == null) DebugElement.throwNullArgumentException("lhs");
		if (rhs == null) DebugElement.throwNullArgumentException("rhs");

		try { switch (op) {
		case Add:			return lhs.add(rhs);
		case Subtract:		return lhs.subtract(rhs);
		case Multiply:		return lhs.multiply(rhs);
		case ShiftLeft:		return lhs.shiftLeft(rhs);
		case BitAnd:		return lhs.bitAnd(rhs);
		case Divide:
		case IntegerDivide:	return lhs.divide(rhs);
		case Modulo:		return lhs.modulo(rhs);
			
		case Max:
			// TODO: (Max ...) Max (Max ...) = lhs.addAll(rhs)
			// TODO: (? ...) Max +infinity = rhs
			// TODO: (? ...) Max -infinity = lhs
			// TODO: (Max ...) Max ? = lhs.add(rhs)
		case Min:
			// TODO: (Min ...) Min (Min ...) = lhs.addAll(rhs)
			// TODO: (? ...) Min +infinity = lhs
			// TODO: (? ...) Min -infinity = rhs
			// TODO: (Min ...) Min ? = lhs.add(rhs)
		default:
			DebugElement.throwTodoException(toString(op, lhs, rhs));
			break;
		} } catch (ReenterException e) {
			throw e;
		} catch (Exception e) {
			DebugElement.throwTodoException(toString(op, lhs, rhs), e);
		}
		
		return null;
	}
	

	
	/**
	 * TODO: merging with {@link Assignable#fromCanonicalIteratorOf(IASTForStatement)}?
	 * TODO? return Expression.from(loop.getIterationExpression()).getConstantPart()
	 * 
	 * @param loop
	 * @param sideEffect
	 * @param condGen 
	 * @return
	 */
	public static ArithmeticExpression fromIncrementOf(IASTForStatement loop, final ASTAddressable rtAddr, VODCondGen condGen) {
		if (loop == null) return null;
		
		IASTExpression exp = loop.getIterationExpression();	// assumed a valid loop iteration expression
		if (exp instanceof IASTUnaryExpression) {
			IASTUnaryExpression uie = (IASTUnaryExpression) exp;
//			if (LValueComputer.getDependentOnBy(uie.getOperand(), it) != null) 
			switch (uie.getOperator()) {
			/* 					++var
			 * 					var++
			 * 					--var
			 * 					var--
			 */
			case IASTUnaryExpression.op_prefixIncr:
			case IASTUnaryExpression.op_postFixIncr:	return Int.ONE;
			case IASTUnaryExpression.op_prefixDecr:
			case IASTUnaryExpression.op_postFixDecr:	return Int.MINUS_ONE;
			}
			
		} else if (exp instanceof IASTBinaryExpression) try {
			final IASTBinaryExpression bie = (IASTBinaryExpression) exp;	// binary incr-expr
			final IASTExpression bieRhs = bie.getOperand2();
//			if (LValueComputer.getDependentOnBy(bie.getOperand1(), it) != null) 
			switch (bie.getOperator()) {
			/* 					var += incr
			 * 					var -= incr
			 */
			case IASTBinaryExpression.op_plusAssign: 
				return Elemental.getSkipNull(()-> (ArithmeticExpression) Expression.fromRecursively(bieRhs, rtAddr, condGen));
			case IASTBinaryExpression.op_minusAssign: 
				return Elemental.getSkipNull(()-> (ArithmeticExpression) Expression.fromRecursively(bieRhs, rtAddr, condGen).minus());
				
			case IASTBinaryExpression.op_assign:
				if (bieRhs instanceof IASTBinaryExpression) {
					final IASTBinaryExpression asgr = (IASTBinaryExpression) bieRhs;	// assigner
					final IASTExpression asgrOp1 = asgr.getOperand1(), 
							asgrOp2 = asgr.getOperand2();
					final IASTName citName = ASTUtil.getNameOf(bie.getOperand1()), 
							asgrOp1Name = ASTUtil.getNameOf(asgrOp1);
					switch (asgr.getOperator()) {
					case IASTBinaryExpression.op_plus:
						// 					var = var + incr
						if (ASTUtil.equals(citName, asgrOp1Name, true)) return Elemental.getSkipNull(()-> 
							(ArithmeticExpression) Expression.fromRecursively(asgrOp2, rtAddr, condGen));
						//					var = incr + var
						if (ASTUtil.equals(citName, ASTUtil.getNameOf(asgrOp2), true)) return Elemental.getSkipNull(()-> 
							(ArithmeticExpression) Expression.fromRecursively(asgrOp1, rtAddr, condGen));
					case IASTBinaryExpression.op_minus:	
						// 					var = var - incr
						if (ASTUtil.equals(citName, asgrOp1Name, true)) return Elemental.getSkipNull(()-> 
							(ArithmeticExpression) Expression.fromRecursively(asgrOp2, rtAddr, condGen).minus());
					}
				}
			}
		} catch (Exception e) {
			DebugElement.throwUnhandledException(e);
		}
		
		return null;
	}
	
	/**
	 * TODO: handling non-canonical loops.
	 * 
	 * @param loop
	 * @param wantsLowerBound
	 * @param condGen 
	 * @return
	 * @throws Exception 
	 */
	static ArithmeticExpression fromBoundOf(IASTForStatement loop, 
			boolean wantsLowerBound, final ASTAddressable rtAddr, VODCondGen condGen) 
			throws ASTException, UncertainException {
		if (loop == null) DebugElement.throwNullArgumentException("loop");
		if (condGen == null) DebugElement.throwNullArgumentException("scope manager");
//		if (scope == null) scope = Function.getScopeOf(loop, condGen);	// lazy scope setting
		
//		LOOP_BOUND_CACHE.clear();
		ArithmeticExpression[] bounds = ASTLoopUtil.getBoundsOf(loop);
		if (bounds != null) return bounds[wantsLowerBound ? 0 : 1];
		
		final IASTInitializerClause ib = 
				ASTLoopUtil.getCanonicalInitialBoundOf(loop);
		final IASTExpression tb = 
				ASTLoopUtil.getCanonicalTestBoundOf(loop, condGen);
		// TODO: suport iterator type of var/bound
		ArithmeticExpression lb = null, ub = null; 
		Expression ibe = Expression.fromRecursively(ib, rtAddr, condGen), 
				tbe = Expression.fromRecursively(tb, rtAddr, condGen); 
		final Int incr = Int.fromCanonicalIncrementOf(loop, rtAddr, condGen);
		final int tbOp = ASTLoopUtil.getCanonicalTestOperatorToVarOf(loop, condGen);
		OrderRelation.Operator orOp;
		
		/* normalization of [ib,test-expr operator,tb] does NOT work
		 * 	-> incr <|>= 0		(doing arithmetic semantics checking of incr here)
		 *  -> ib <|<|>|>= tb	(leaving arithmetic semantics checking to Z3)
		 */
		try {
		if (tests(incr.isPositiveOrZero())) switch (tbOp) {
		case IASTBinaryExpression.op_lessThan:
			/*
			 * tb[Or1:e0]	<	(var =	ib[Or2:e1])	&& var += |incr|
			 * (ib			=	var) >	tb			&& var += |incr|
			 * 
			 * 	=>	lb = ib[Or2:e1], 
			 * 		ub = (tb[Or1:e0] < ib[Or2:e1]) ? +oo : ib[Or2:e1]
			 */
			orOp = OrderRelation.Operator.LessThan;
			
		case IASTBinaryExpression.op_lessEqual:
			/*
			 * tb			<=	(var =	ib)			&& var += |incr|
			 * (ib			=	var) >=	tb			&& var += |incr|
			 * 
			 * 	=>	lb = ib[Or2:e1], 
			 * 		ub = (tb[Or1:e0] <= ib[Or2:e1]) ? +oo : ib[Or2:e1]
			 */
			orOp = OrderRelation.Operator.LessEqual;
			final OrderRelation.Operator orOp_ = orOp;
			final Expression tbe_ = tbe;
			lb = getSkipNull(()-> (ArithmeticExpression) ibe);
			ub = getSkipNull(()-> (ArithmeticExpression) ConditionalExpression.from(
					OrderRelation.from(orOp_, tbe_, ibe, null), Int.POSITIVE_INFINITY, ibe));
			break;
			
		case IASTBinaryExpression.op_greaterThan:
			/*
			 * (ib	=	var) <	tb	&& var += |incr|
			 * tb	>	(var =	ib)	&& var += |incr|
			 * 
			 * 	=>	lb = ib,
			 * 		ub = (ib < tb) ? tb-1 : ib
			 */
			final Expression tbe__ = tbe;
			lb = getSkipNull(()-> (ArithmeticExpression) ibe);
			ub = getSkipNull(()-> (ArithmeticExpression) ConditionalExpression.from(
					OrderRelation.from(OrderRelation.Operator.LessThan, ibe, tbe__, null), 
					Arithmetic.from(Operator.Subtract, tbe__, Int.ONE), 
					ibe));
			break;
			
		case IASTBinaryExpression.op_greaterEqual:
			/* 
			 * (ib			=	var) <=	tb			&& var += |incr|
			 * tb			>=	(var =	ib)			&& var += |incr|
			 * 
			 * 	=>	lb = ib,
			 * 		ub = (ib 		 <= tb) ? tb : ib
			 */
			final Expression tbe___ = tbe;
			lb = getSkipNull(()-> (ArithmeticExpression) ibe);
			ub = getSkipNull(()-> (ArithmeticExpression) ConditionalExpression.from(
					OrderRelation.from(OrderRelation.Operator.LessEqual, ibe, tbe___, null), tbe___, ibe));
			break;
			
		} else switch (tbOp) {
		case IASTBinaryExpression.op_lessThan:
			/*
			 * tb			<	(var =	ib[Or2:e1])	&& var -= |incr|
			 * (ib			=	var) >	tb			&& var -= |incr|
			 * 
			 * 	=>	lb = (ib[Or2:e1] < tb[Or1:e0]) ? ib[Or2:e1] : tb[Or1:e0]+1,
			 * 		ub = ib[Or2:e1]
			 */
			orOp = OrderRelation.Operator.LessThan;
			if (tbe instanceof ArithmeticExpression)
				tbe = (Expression) ((ArithmeticExpression) tbe).add(Int.ONE);
			else DebugElement.throwTodoException(
					tbe.toString() + " should be ArithmeticExpression!");
			
		case IASTBinaryExpression.op_lessEqual:
			/*
			 * tb			<=	(var =	ib)			&& var -= |incr|
			 * (ib			=	var) >=	tb			&& var -= |incr|
			 * 
			 * 	=>	lb = (ib <= tb) ? ib : tb,
			 * 		ub = ib
			 */
			orOp = OrderRelation.Operator.LessEqual;
			final OrderRelation.Operator orOp_ = orOp;
			final Expression tbe_ = tbe;
			lb = getSkipNull(()-> (ArithmeticExpression) 
					ConditionalExpression.from(
					OrderRelation.from(orOp_, ibe, tbe_, null), ibe, tbe_));
			ub = getSkipNull(()-> (ArithmeticExpression) ibe);
			break;
			
		case IASTBinaryExpression.op_greaterThan:
			/*
			 * (ib			=	var) <	tb			&& var -= |incr|
			 * tb			>	(var =	ib)			&& var -= |incr|
			 * 
			 * 	=>	lb = (ib[Or1:e0] < tb[Or2:e1]) ? -oo : ib[Or1:e0],
			 * 		ub = ib[Or1:e0]
			 */
			orOp = OrderRelation.Operator.LessThan;
			
		case IASTBinaryExpression.op_greaterEqual:
			/*
			 * (ib			=	var) <=	tb			&& var -= |incr|
			 * tb			>=	(var =	ib)			&& var -= |incr|
			 * 
			 * 	=>	lb = (ib[Or1:e0] <= tb[Or2:e1]) ? -oo : ib[Or1:e0],
			 * 		ub = ib[Or1:e0]
			 */
			orOp = OrderRelation.Operator.LessEqual;
			final OrderRelation.Operator orOp__ = orOp;
			final Expression tbe__ = tbe;
			lb = getSkipNull(()-> (ArithmeticExpression) 
					ConditionalExpression.from(
					OrderRelation.from(orOp__, ibe, tbe__, null), 
					Int.NEGATIVE_INFINITY, ibe));
			ub = getSkipNull(()-> (ArithmeticExpression) ibe);
			break;
		}
		
		} catch (ASTException | UncertainException e) {
			throw e;
		} catch (Exception e) {
			DebugElement.throwUnhandledException(e);
		}
		ASTLoopUtil.setBoundsOf(loop, bounds = new ArithmeticExpression[] {lb, ub});
		return wantsLowerBound ? lb : ub;
	}
	
	/**	<pre>
	 * 		test-expr	One of the following:
	 * 					var relational-op tb
	 * 					tb relational-op var
	 * <br>
	 * 
	 * @param loop
	 * @param condGen 
	 * @return
	 * @throws Exception 
	 */
	public static ArithmeticExpression fromLowerBoundOf(
			IASTForStatement loop, final ASTAddressable rtAddr, VODCondGen condGen) {
		return fromBoundOf(loop, true, rtAddr, condGen);
	}
	
	public static ArithmeticExpression fromUpperBoundOf(
			IASTForStatement loop, final ASTAddressable rtAddr, VODCondGen condGen) {
		return fromBoundOf(loop, false, rtAddr, condGen);
	}
	
	
	
	static public <T> T getSkipNull(Supplier<T> sup) {
		return Elemental.getSkipNull(sup);
	}

	
	
	static public boolean tests(Boolean tester) {
		return Elemental.tests(tester);
	}
	
	default public boolean containsArithmetic() {
		return true;
	}
	
	
	
	default public boolean contains(ArithmeticExpression ae2) {
		return ae2 != null && toExpression().contains(ae2.toExpression());
	}
	
	default public boolean contains(PathVariablePlaceholder pvp) {
		return pvp != null && toExpression().contains(pvp);
	}
	
	default public boolean contains(Iterable<Assignable<?>> asns) {
		if (asns != null) 
			for (Assignable<?> asn : asns)
				if (contains(asn.getPathVariablePlaceholder())) return true;

		return false;
	}
	

	
	default public boolean derives(ThreadRoleMatchable matchable2) {
		final boolean sd = ThreadRoleMatchable.super.derives(matchable2);
		return matchable2 instanceof ArithmeticExpression
				? sd || derives(((ArithmeticExpression) matchable2).getDirectVariableReferences())
				: sd;
	}
	
	default public boolean derives(Collection<ArithmeticExpression> ae2s) {
		if (ae2s == null) DebugElement.throwNullArgumentException("arithmetic expression");
		
		for (ArithmeticExpression ae2 : ae2s) 
			if (derives(ae2) || derives(ae2.getDirectVariableReferences())) return true;
		return false;
	}

	default public boolean derives(Set<Version<?>> vers) {
		return Version.derives(getDirectVariableReferences(), vers);
	}
	
	

	default public boolean isUnary() {
		return this instanceof Relation
				? ((Relation) this).isUnary()
				: true;
//		DebugElement.throwTodoException("unsupported arithmetic expression");
	}
	
	@Override
	default public boolean isPrivate() {
		return ThreadRoleMatchable.super.isPrivate();
	}
	
	@SuppressWarnings("unchecked")
	@Override
	default public Boolean isNegativeInfinity() 
			throws ReenterException {
		return trySkipNullException(
				getMethod(ArithmeticExpression.class, "isNegativeInfinity"),
				()-> NumericExpression.super.isNegativeInfinity(),
				// main return
				()-> getZero().subtract(this).isPositiveInfinity());
	}

	
	
	@SuppressWarnings({ "unchecked" })
	default public ArithmeticExpression add(ArithmeticExpression addend) {
		if (addend == null) DebugElement.throwNullArgumentException("addend");

		final Number<?> ZERO = getZero(addend);
		try {
			return trySkipNullException(
					// 0 + (? ...) = rhs
					()-> isZero() ? addend : null,
					// (? ...) + 0 = lhs
					()-> addend.isZero() ? this : null,
					// x + (? - x) = ?
					()-> addSubtract(addend),
					// (? - x) + x = ?
					()-> addend.addSubtract(this),
					()-> applyConst(con-> con.add(addend), ()-> (ArithmeticExpression) toNonSelfConstant()),
					()-> applyConst(con-> add(con), ()-> (ArithmeticExpression) addend.toNonSelfConstant()),

					// oo + -oo = 0, oo + ? = oo
					()-> isPositiveInfinity() ? 
							(addend.isNegativeInfinity() ? ZERO : this) : null,
					// -oo + oo = 0, -oo + ? = -oo
					()-> isNegativeInfinity() ? 
							(addend.isPositiveInfinity() ? ZERO : this) : null,
					()-> Arithmetic.from(Operator.Add, this, addend));
			
		} catch (Exception e) {
			return DebugElement.throwUnhandledException(e);
		} 
	}
	
	/**
	 * @param subtract - assumed in form s1 - s2
	 * @return aRest if this is at + aRest and at == s2.
	 */
	default public ArithmeticExpression addSubtract(ArithmeticExpression subtract) {
		final Arithmetic a = (Arithmetic) this, s = (Arithmetic) subtract;
		if (subtract == null || !s.getOp().equals(Operator.Subtract)) 
			return throwNullArithmeticException("subtraction expression");
		
		final Expression s1 = s.getOperand1(), s2 = s.getOperand2();
		if (a.getOp().equals(Operator.Add)) {
			for (Expression at : a.getOperands()) if (at.equals(s2)) {
				final Arithmetic ass = (Arithmetic) a.rest(at);
				return ass.add(s1)
						? ass
						: DebugElement.throwTodoException("unsupported list");
			}
			return null;
		}
		
		return DebugElement.throwTodoException("unsupported augend");
	}
	

	
	@SuppressWarnings("unchecked")
	default public ArithmeticExpression subtract(ArithmeticExpression subtrahend) 
			throws ReenterException {
		if (subtrahend == null) DebugElement.throwNullArgumentException("subtrahend");

		final Number<?> ZERO = getZero(subtrahend);
		/* breaking isNegativeInfinity()-subtract(this)-subtrahend.isNegative() 
		 * and minus()/negate()-subtract(this) cycles
		 */
		try {
			return trySkipNullException(
					// (? ...) - 0 = lhs
					()-> subtrahend.isZero() ? this : null,
					// 0 - (- ...) = -rhs
					()-> isZero() && subtrahend.isNegative() ? 
							(ArithmeticExpression) subtrahend.negate() : null,
					// x - (? + x) = ?
					()-> subtractAdd(subtrahend),
					// (? + x) - x = ?
					()-> subtractByAugend(subtrahend),
					()-> applyConst(con-> con.subtract(subtrahend), ()-> (ArithmeticExpression) toNonSelfConstant()),
					()-> applyConst(con-> subtract(con), ()-> (ArithmeticExpression) subtrahend.toNonSelfConstant()),

					// oo - oo = 0, oo - ? = oo
					()-> isPositiveInfinity() ? 
							(subtrahend.isPositiveInfinity() ? ZERO : this) : null,
					// -oo - -oo = 0, -oo - ? = -oo
					()-> isNegativeInfinity() ? 
							(subtrahend.isNegativeInfinity() ? ZERO : this) : null,
					// TODO: (- ...) - ? = lhs.add(rhs)
					()-> Arithmetic.from(Operator.Subtract, this, subtrahend));
			
		} catch (ReenterException e) {
			throw e;
		} catch (Exception e) {
			return DebugElement.throwUnhandledException(e);
		} 
	}
	
	/**
	 * @param subtrahend
	 * @return aRest if this is at + aRest and at == subtrahend.
	 */
	@SuppressWarnings("unlikely-arg-type")
	default public ArithmeticExpression subtractByAugend(ArithmeticExpression subtrahend) {
		if (subtrahend == null) DebugElement.throwNullArgumentException("subtrahend");

		final Arithmetic a = (Arithmetic) this;
		if (a.getOp().equals(Operator.Add)) 
			for (Expression at : a.getOperands()) 
				if (subtrahend.equals(at)) return (ArithmeticExpression) a.rest(at);
		return null;
	}
	
	/**
	 * @param add - at + aRest
	 * @return -aRest if this is at.
	 */
	@SuppressWarnings("unlikely-arg-type")
	default public ArithmeticExpression subtractAdd(ArithmeticExpression add) {
		if (add == null) return throwNullArithmeticException("addition expression");
		
		final Arithmetic a = (Arithmetic) add;
		if (a.getOp().equals(Operator.Add)) 
			for (Expression at : a.getOperands()) 
				if (equals(at)) return (ArithmeticExpression) a.rest(at).negate();
		return null;
	}
	
	
	
	@SuppressWarnings("unchecked")
	default public ArithmeticExpression multiply(ArithmeticExpression multiplicand) 
			throws UncertainException {
		if (multiplicand == null) DebugElement.throwNullArgumentException("multiplicand");

		final Number<?> ZERO = getZero(multiplicand);
		if (ZERO == null) DebugElement.throwTodoException("unsupported zero type");
		final Number<?> OO = ZERO.getPositiveInfinity(), NOO = ZERO.getNegativeInfinity();
		try {
			return trySkipNullException(
					// 0 * A = A * 0 = 0
					()-> isZero() || multiplicand.isZero() ? ZERO : null,
					// 1 * A = A
					()-> isOne() ? multiplicand : null,
					// A * 1 = A
					()-> multiplicand.isOne() ? this : null,
					()-> applyConst(con-> con.multiply(multiplicand), ()-> (ArithmeticExpression) toNonSelfConstant()),
					()-> applyConst(con-> multiply(con), ()-> (ArithmeticExpression) multiplicand.toNonSelfConstant()),

					// locally defining for breaking isNegative()-subtract(...) cycle
					// oo * (-) = -oo, oo * (+) = oo
					()-> isPositiveInfinity() ? 
							(multiplicand.isNegative() ? NOO : OO) : null,
					// (-) * oo = -oo, (+) * oo = oo
					()-> multiplicand.isPositiveInfinity() ? 
							(isNegative() ? NOO : OO) : null,
					// -oo * (-) = oo, -oo * (+) = -oo
					()-> isNegativeInfinity() ? 
							(multiplicand.isNegative() ? OO : NOO) : null,
					// (-) * -oo = oo, (+) * -oo = -oo
					()-> multiplicand.isNegativeInfinity() ? 
							(isNegative() ? OO : NOO) : null,
					()-> Arithmetic.from(Operator.Multiply, this, multiplicand));
			
		} catch (UncertainException e) {
			throw e;
		} catch (Exception e) {
			return DebugElement.throwUnhandledException(e);
		} 
	}
	
	@SuppressWarnings("unchecked")
	default public ArithmeticExpression bitAnd(ArithmeticExpression ae2) {
		if (ae2 == null) DebugElement.throwNullArgumentException("exponent");
		
		final Number<?> ZERO = getZero(ae2);
		if (ZERO == null) DebugElement.throwTodoException("unsupported zero type");
//		final Number<?> OO = ZERO.getPositiveInfinity(), NOO = ZERO.getNegativeInfinity();
		try {
			return trySkipNullException(
					// 0 & A = 0
					()-> isZero() ? ZERO : null,
					// A & 0 = 0
					()-> ae2.isZero() ? ZERO : null,
					// 1 & A = A
					()-> isOne() ? ae2 : null,
					// A & 1 = A
					()-> ae2.isOne() ? this : null,
							
					()-> applyConst(con-> con.bitAnd(ae2), ()-> (ArithmeticExpression) toNonSelfConstant()),
					()-> applyConst(con-> bitAnd(con), ()-> (ArithmeticExpression) ae2.toNonSelfConstant()),
					()-> Arithmetic.from(Operator.BitAnd, this, ae2));
			
//		} catch (UncertainException e) {
//			throw e;
		} catch (Exception e) {
			return DebugElement.throwUnhandledException(e);
		} 
	}
	
	@SuppressWarnings("unchecked")
	default public ArithmeticExpression shiftLeft(ArithmeticExpression exponent) {
		if (exponent == null) DebugElement.throwNullArgumentException("exponent");
		
		final Number<?> ZERO = getZero(exponent);
		if (ZERO == null) DebugElement.throwTodoException("unsupported zero type");
//		final Number<?> OO = ZERO.getPositiveInfinity(), NOO = ZERO.getNegativeInfinity();
		try {
			return trySkipNullException(
					// 0 << A = 0
					()-> isZero() ? ZERO : null,
					// A << 0 = A
					()-> exponent.isZero() ? this : null,
					()-> applyConst(con-> con.shiftLeft(exponent), ()-> (ArithmeticExpression) toNonSelfConstant()),
					()-> applyConst(con-> shiftLeft(con), ()-> (ArithmeticExpression) exponent.toNonSelfConstant()),
					
					// locally defining for breaking isNegative()-subtract(...) cycle
//					// oo * (-) = -oo, oo * (+) = oo
//					()-> isPositiveInfinity() ? (exponent.isNegative() ? NOO : OO) : null,
//					// (-) * oo = -oo, (+) * oo = oo
//					()-> exponent.isPositiveInfinity() ? (isNegative() ? NOO : OO) : null,
//					// -oo * (-) = oo, -oo * (+) = -oo
//					()-> isNegativeInfinity() ? (exponent.isNegative() ? OO : NOO) : null,
//					// (-) * -oo = oo, (+) * -oo = -oo
//					()-> exponent.isNegativeInfinity() ? (isNegative() ? OO : NOO) : null,
					()-> Arithmetic.from(Operator.ShiftLeft, this, exponent));
			
//		} catch (UncertainException e) {
//			throw e;
		} catch (Exception e) {
			return DebugElement.throwUnhandledException(e);
		} 
	}
	
	@SuppressWarnings("unchecked")
	default public ArithmeticExpression divide(ArithmeticExpression divisor) 
			throws UncertainException {
		if (divisor == null) DebugElement.throwNullArgumentException("divisor");
		
		final Number<?> ZERO = getZero(divisor);
		try {
			return trySkipNullException(
					// 0 / A = 0
					()-> isZero() ? ZERO : null,
					// ? / 0 = exception
					()-> divisor.isZero() ? DebugElement.throwTodoException("Divide by zero!") : null,
					()-> applyConst(con-> con.divide(divisor), ()-> (ArithmeticExpression) toNonSelfConstant()),
					()-> applyConst(con-> divide(con), ()-> (ArithmeticExpression) divisor.toNonSelfConstant()),
					()-> Arithmetic.from(Operator.Divide, this, divisor));
//	TODO, type-checking:()-> Arithmetic.from(Operator.IntegerDivide, this, divisor));

		} catch (UncertainException e) {
			throw e;
		} catch (Exception e) {
			return DebugElement.throwUnhandledException(e);
		} 
	}
	
	@SuppressWarnings("unchecked")
	default public ArithmeticExpression modulo(ArithmeticExpression modulus) 
			throws UncertainException {
		if (modulus == null) DebugElement.throwNullArgumentException("modulus");
		
		final Number<?> ZERO = getZero(modulus);
		try {
			return trySkipNullException(
					// 0 % A = 0
					()-> isZero() ? ZERO : null,
					// ? % 0 = exception
					()-> modulus.isZero() ? DebugElement.throwTodoException("Modulo by zero!") : null,
					()-> applyConst(con-> con.modulo(modulus), ()-> (ArithmeticExpression) toNonSelfConstant()),
					()-> applyConst(con-> modulo(con), ()-> (ArithmeticExpression) modulus.toNonSelfConstant()),
					()-> Arithmetic.from(Operator.Modulo, this, modulus));

		} catch (UncertainException e) {
			throw e;
		} catch (Exception e) {
			return DebugElement.throwUnhandledException(e);
		} 
	}
	
	default public Expression negate() 
			throws ReenterException, UnsupportedOperationException {
		try {
		final Expression result = NumericExpression.super.negate();
		return result != null 
				? result 
				: Elemental.getThrow(()-> 
				(Expression) getZero().subtract(this));
		
		} catch (ReenterException e) {
			throw e;
		} catch (ClassCastException e) {
			return SystemElement.throwUnsupportedNegation();
		} catch (Exception e) {
			return DebugElement.throwUnhandledException(e);
		}
	}
	
	
	
//	default public <T extends ConditionElement> T cloneIfChangeRole(
//			final ThreadRoleMatchable role) {
//		return toExpression().cloneIfChangeRole(role);
//	}
	
	default public ArithmeticExpression cloneReindex(VariablePlaceholder<?> oldIndex, VariablePlaceholder<?> newIndex) {
		return ((Expression) toExpression().clone()).substitute(oldIndex, newIndex);
	}
	
	default public <T extends ConditionElement> T cloneReversion(
			final IASTStatement blockStat, final FunctionallableRole role, Version<? extends PathVariable> ver) {
		return toExpression().cloneReversion(blockStat, role, ver);
	}
	
	
	
	default public <T> T throwNullArithmeticException(String message) {
//		return null;
		if (message == null) message = "arithmetic expression";
		return DebugElement.throwNullArgumentException(message);
//		TODO: throw new NullArithmeticException(); super("null Arithmetic");
	}
	
	
	
	public static String toString(
			Operator op, ArithmeticExpression lhs, ArithmeticExpression rhs) {
		return lhs == null ? "(null)" : lhs.toString() 
				+ " " + op == null ? "(null)" : op.toString() 
				+ " " + rhs == null ? "(null)" : rhs.toString();
	}
	
	/**
	 * @param printsVariableDeclaration
	 * @param printsFunctionDefinition
	 * @param isLhs TODO
	 * @return
	 */
	public String toZ3SmtString(
			boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs);

}