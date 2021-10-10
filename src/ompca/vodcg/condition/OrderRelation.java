/**
 * @author Kao, Chen-yi
 *
 */
package ompca.vodcg.condition;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.EnumMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import ompca.DebugElement;
import ompca.DuoKeyMap;
import ompca.Elemental;
import ompca.Mappable;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.data.Number;
import ompca.vodcg.condition.data.NumericExpression;
import ompca.vodcg.condition.data.PlatformType;

/**
 * OrderRelation	::= VariableRange | Equality | Expression ('='|'!='|'<'|'>'|'<='|'>=') Expression
 * 
 * TODO:			::= Expression ('!=' Expression)+
 * TODO:			::= Expression ('<' Expression)+
 * TODO:			::= Expression ('>' Expression)+
 * TODO:			::= Expression ('<=' Expression)+
 * TODO:			::= Expression ('>=' Expression)+
 * 
 */
@SuppressWarnings("deprecation")
public class OrderRelation extends Proposition {

	public enum Operator implements Relation.Operator {
		Equal, NotEqual, LessThan, GreaterThan, LessEqual, GreaterEqual;

		/* (non-Javadoc)
		 * @see ompca.condition.Relation.Operator#isAssociativeTo(ompca.condition.Relation.Operator)
		 */
		@Override
		public boolean isAssociativeTo(Relation.Operator op) {
//			switch (this) {
//			case Equal:			// T != (F != (T = T)) => F, ((T != F) != T) = T => F, ...
//			case LessThan:		// either domain and range are in different types 
//			case GreaterThan:	//	or the Proposition order is not defined
//			case LessEqual:		
//			case GreaterEqual:	
//			case NotEqual:	
//			default:			
				return false;	// since the relational result and expression operands are in different domains
//			}
		}
		
		public boolean isCommutative() {
			switch (this) {
			case Equal:
			case NotEqual:		return true;	
			case LessThan: 
			case GreaterThan:
			case LessEqual:		
			case GreaterEqual:	
			default:			return false;
			}
		}
		


		@Override
		public <M extends Map<?,?>> EnumMap<? extends Key, M> createPartitionMap() {
			return new EnumMap<>(Operator.class);
		}
		
		@Override
		public <M extends Mappable<?, ?>> EnumMap<? extends Key, M> createPartitionMappable() {
			return new EnumMap<>(Operator.class);
		}



		/* (non-Javadoc)
		 * @see ompca.condition.Relation.Operator#negate()
		 */
		@Override
		public ompca.vodcg.condition.Relation.Operator negate() {
			switch (this) {
			case Equal:			return NotEqual;
			case LessThan:		return GreaterEqual;
			case GreaterThan:	return LessEqual;
			case LessEqual:		return GreaterThan;
			case GreaterEqual:	return LessThan;
			case NotEqual:		return Equal;
			default:
				assert(false); return null;	// should NOT come here!
			}
		}

		
		
		public String toString() {
			switch (this) {
			case Equal:			
			case LessThan:		
			case GreaterThan:	
			case LessEqual:		
			case GreaterEqual:	return toZ3SmtString(null, false, false);
			case NotEqual:		return "!=";
			default:
				assert(false); return null;	// should NOT come here!
			}
		}
		
		public <H extends Relation> String toZ3SmtString(
				H host, boolean printsVariableDeclaration, boolean printsFunctionDefinition) {
			switch (this) {
			case Equal:			return "=";
			case LessThan:		return "<";
			case GreaterThan:	return ">";
			case LessEqual:		return "<=";
			case GreaterEqual:	return ">=";
			case NotEqual:		return "not (=";
			default:
				assert(false); return null;	// should NOT come here!
			}
		}

	}



	final static private DuoKeyMap<Expression,Expression,Proposition> 
	EQ_CACHE = new DuoKeyMap<>();
	final static private DuoKeyMap<Expression,Expression,Proposition> 
	GE_CACHE = new DuoKeyMap<>();
	final static private DuoKeyMap<Expression,Expression,Proposition> 
	GT_CACHE = new DuoKeyMap<>();
	final static private DuoKeyMap<Expression,Expression,Proposition> 
	LE_CACHE = new DuoKeyMap<>();
	final static private DuoKeyMap<Expression,Expression,Proposition> 
	LT_CACHE = new DuoKeyMap<>();
	final static private DuoKeyMap<Expression,Expression,Proposition> 
	NE_CACHE = new DuoKeyMap<>();
	final static private Map<Operator, DuoKeyMap<Expression,Expression,Proposition>> 
	OPERATION_CACHE = new EnumMap<>(Operator.class);
	
	private static final Method METHOD_GET = Elemental.getMethod(OrderRelation.class, "from", 
			Operator.class, Expression.class, Expression.class, Supplier.class);
	private static final Method METHOD_AND_BY_REDUCE = Elemental.getMethod(OrderRelation.class, "andByReduce", 
			OrderRelation.class);
	
	
	
//	protected OrderRelation(Operator operator, Collection<Expression> operands, 
//			VOPCondGen scopeManager) {
//		super(operator, operands, scopeManager);
////		init();
//	}
	
	/**
	 * A convenient triple-operands constructor.
	 * 
	 * @param operator
	 * @param left_operand
	 * @param mid_operand
	 * @param right_operand
	 */
	protected OrderRelation(Operator operator, Expression left_operand, 
			Expression mid_operand, Expression right_operand) {
		this(operator, checkOperands(Arrays.asList(left_operand, mid_operand, right_operand)), left_operand.getScopeManager());
	}
	
	/**
	 * Specific constructor for {@link Equality} and binary in-equality.
	 * 
	 * TODO: also for n-ary in-equality if total in-equivalence applied.
	 *  
	 * @param operator
	 * @param operands
	 * @param scope
	 * @param scopeManager
	 */
	protected OrderRelation(Operator operator, Set<Expression> operands, 
			VODCondGen scopeManager) {
		super(operator, checkOperands(operands), scopeManager);

		if (!operator.isCommutative()) 
			returnTodoException("Set operands are for commutative (non-monotonic) order relations ONLY!");
	}
	
	protected OrderRelation(Operator operator, List<Expression> operands, 
			VODCondGen scopeManager) {
		super(operator, checkOperands(operands), scopeManager);
		
		assert operands != null;
		if (isUnary()) throwInvalidityException("order is not necessary");
	}
	
	private OrderRelation(Operator operator, Expression lhs, Expression rhs) {
		this(operator, checkOperands(lhs, rhs), lhs.getScopeManager());
	}
	

	
//	@SuppressWarnings("unchecked")
//	private void init() {
//		exps = (Collection<Expression>) operands;
//	}
	
	
	
	/**
	 * This factory method includes {@link Equality#from(int, Expression, Expression)}
	 * since {@link Operator} includes {@link Operator#Equal}.
	 * Non-assignments have NO side-effects of their own to propagate outwards.
	 * @param expOp - pre-cached operator of exp
	 * @param lhs 	- pre-cached left-hand-side of exp
	 * @param rhs 	- pre-cached right-hand-side of exp
	 * 
	 * @return
	 */
	public static Proposition fromRecursively(int expOp, Expression lhs, Expression rhs) {
		if (lhs == null) throwNullArgumentException("lhs");
		if (rhs == null) throwNullArgumentException("rhs");
		
		Operator op = null;
		switch (expOp) {
		// >=
		case IASTBinaryExpression.op_greaterEqual:	op = Operator.GreaterEqual; break;
		// >
		case IASTBinaryExpression.op_greaterThan:	op = Operator.GreaterThan; break;
		// <=
		case IASTBinaryExpression.op_lessEqual:		op = Operator.LessEqual; break;
		// <
		case IASTBinaryExpression.op_lessThan:		op = Operator.LessThan; break;
		// !=: TODO creating Inequality class with Set of operands?
		case IASTBinaryExpression.op_notequals:		op = Operator.NotEqual; break;
		}

		if (op != null) {
//			if (Elemental.tests(()-> lhs.isConstant() && rhs.isConstant())) throwReductionException();
			return from(op, lhs, rhs, null);
		}
		return Equality.from(expOp, lhs, rhs);
	}

	/**
	 * The equality relation should NOT be interpreted as proposition true.
	 * Therefore only identical object operand is reduce-able.
	 *  
	 * @param op
	 * @param lhs - assumed of ordered type in the number theory
	 * @param rhs - assumed of ordered type in the number theory
	 * @param constructor 
	 * @return
	 */
	public static Proposition from(Operator op, Expression lhs, Expression rhs, Supplier<OrderRelation> constructor) {
		if (op == null) throwNullArgumentException("op");
		if (lhs == null) throwNullArgumentException("lhs");
		if (rhs == null) throwNullArgumentException("rhs");
		
		lhs = (Expression) lhs.reduce(METHOD_GET); 
		rhs = (Expression) rhs.reduce(METHOD_GET);
		
		if (OPERATION_CACHE.isEmpty()) {
			OPERATION_CACHE.put(Operator.Equal,			EQ_CACHE);
			OPERATION_CACHE.put(Operator.GreaterEqual,	GE_CACHE);
			OPERATION_CACHE.put(Operator.GreaterThan,	GT_CACHE);
			OPERATION_CACHE.put(Operator.LessEqual,		LE_CACHE);
			OPERATION_CACHE.put(Operator.LessThan,		LT_CACHE);
			OPERATION_CACHE.put(Operator.NotEqual,		NE_CACHE);
		}
		final DuoKeyMap<Expression,Expression,Proposition> opCache = 
				OPERATION_CACHE.get(op);
		Proposition or = opCache.get(lhs, rhs);
		if (or != null) return or;

//		if (lhs instanceof Number && rhs instanceof Number) throwReductionException();
		if (lhs instanceof NumericExpression && rhs instanceof NumericExpression) 
			or = NumericExpression.from(
					op, (NumericExpression) lhs, (NumericExpression) rhs);
		if (or != null) return or;
		
		switch (op) {
		case GreaterEqual:
		case LessEqual:
		case Equal:		if (lhs == rhs) or = True.from(op, lhs, rhs); break;
		case GreaterThan:
		case LessThan:
		case NotEqual:	if (lhs.equals(rhs)) or = False.from(op, lhs, rhs); break;
		default:
			break;
		}
		if (or != null) return or;
		
//		lhs.checkDependency(op, rhs);
//		rhs.checkDependency(op, lhs);	// for and/or/iff -> setOnlyOperand(...)
		if (constructor != null) or = constructor.get();
		else or = op.equals(Operator.Equal) ? 
				Equality.from(lhs, rhs) : new OrderRelation(op, lhs, rhs);
		if (!or.getOp().equals(op)) returnTodoException("unsupported constructor");

//		opCache.put(ps, result);	// caching the most reduced result at last
		opCache.put(lhs, rhs, or);
		return or;
	}
	
	public static Proposition from(Operator op, Collection<? extends Expression> operands) {
		if (op == null) throwNullArgumentException("op");
		if (operands == null || operands.isEmpty()) throwNullArgumentException("operands");
		
		// expression range reduction
		final int oSize = operands.size();
		if (oSize == 1) throwInvalidityException("single operand");
		else if (oSize == 3 && operands instanceof List) {
			final List<? extends Expression> oList = (List<? extends Expression>) operands;
			final Expression e1 = oList.get(0), e2 = oList.get(1), e3 = oList.get(2);
			if (e1 instanceof ArithmeticExpression 
					&& !(e2 instanceof ArithmeticExpression) 
					&& e3 instanceof ArithmeticExpression) 
				return ExpressionRange.from(e2, (ArithmeticExpression) e1, (ArithmeticExpression) e3);
		}
		
//		boolean isc = true;
		Expression e1 = null;
		Proposition result = null;
		for (Expression e2 : operands) {
			if (e2 == null) throwNullArgumentException("operands");
			if (e1 != null) {
				final Expression e1_ = e1;
				final Supplier<Proposition> biResult = 
						()-> from(op, e1_, e2, null);
				result = result == null ? 
						biResult.get() : result.and(biResult);
			}
			e1 = e2;
//			isc &= Elemental.tests(e2.isConstant());
		}
//		assert operands != null && !operands.isEmpty();
//		if (isc && !op.equals(Operator.Equal)) throwReductionException();
		return result;
	}

	
	
	static private Set<Expression> checkOperands(Set<Expression> operands) {
		if (operands == null || operands.isEmpty()) throwNullArgumentException("operands");
		
		// type checking
		return getType(operands) != null ? 
				operands : (Set<Expression>) checkType(operands, new HashSet<>());
	}
	
	static private List<Expression> checkOperands(List<Expression> operands) {
		if (operands == null || operands.isEmpty()) throwNullArgumentException("operands");
		
		final int size = operands.size();
		for (int i = 0; i < size; i++) 
			if (operands.subList(i + 1, size).contains(operands.get(i)))
					throwReductionException();
		
		// type checking
		return getType(operands) != null ? 
				operands : (List<Expression>) checkType(operands, new ArrayList<>());
	}
	
	static private List<Expression> checkOperands(Expression lhs, Expression rhs) {
		assert lhs != null && rhs != null; 
		if (lhs instanceof Number && rhs instanceof Number) 
			throwReductionException();
		
		return checkOperands(Arrays.asList(lhs, rhs));
	}
	
	static private Collection<Expression> checkType(Collection<Expression> operands, Collection<Expression> checkOperands) {
		assert operands != null && checkOperands.isEmpty() && getType(operands) == null;
		PlatformType t = null;
		for (Expression e : operands) {
			final PlatformType et = e.getType();
			if (t == null) t = et;
			else if (!et.equals(t)) {
				if (et.isCastableTo(t)) e = new CastCall(t, e);
				else throwTodoException("unsupported casting");
			}
			checkOperands.add(e);
		}
		return checkOperands;
	}
	
	static private PlatformType getType(Collection<Expression> operands) {
		assert operands != null;
		PlatformType t = null;
		for (Expression e : operands) {
			final PlatformType et = e.getType();
			if (t == null) t = et;
			else if (t != et) return null;
		}
		return t;
	}
	
	
	
	public PlatformType getDomainType() {
		return getFirstOperand().getType();
	}
	
	public Expression getLowerBound() {
		@SuppressWarnings("unchecked")
		List<Expression> expList = (List<Expression>) toList();
		switch ((Operator) getOp()) {
		case LessThan:
		case LessEqual: 	
			return expList.get(0);
		case GreaterThan:
		case GreaterEqual: 	
			return expList.get(expList.size() - 1);
		default: 			
		}
		return null;
	}
	
	public Expression getUpperBound() {
		@SuppressWarnings("unchecked")
		List<Expression> expList = (List<Expression>) toList();
		switch ((Operator) getOp()) {
		case LessThan:
		case LessEqual: 	
			return expList.get(expList.size() - 1);
		case GreaterThan:
		case GreaterEqual: 	
			return expList.get(0);
		default: 			
		}
		return null;
	}
	
	public Collection<? extends Expression> getPlatformBoundedOperands() {
		return getDomainType().isPlatformBounded() 
				? getOperands() 
				: unboundInfinity(toList());
	}
	
	private Collection<? extends Expression> unboundInfinity(List<? extends Expression> oprds) {
		assert oprds != null;
		final int os = oprds.size();
		final boolean oiu = os == 1;
		final Expression lb = getLowerBound(), ub = getUpperBound();
		final List<? extends Expression> el = Collections.emptyList();
		
		if (lb != null && lb instanceof NumericExpression && Elemental.tests(((NumericExpression) lb).isNegativeInfinity())) 
			switch ((Operator) getOp()) {
			case LessThan:
			case LessEqual:
				return oiu ? el : unboundInfinity(oprds.subList(1, os));
			case GreaterThan:
			case GreaterEqual: 	
				return oiu ? el : unboundInfinity(oprds.subList(0, os-1));
			default: 			
			}

		if (ub != null && ub instanceof NumericExpression && Elemental.tests(((NumericExpression) ub).isPositiveInfinity())) 
			switch ((Operator) getOp()) {
			case LessThan:
			case LessEqual:
				return oiu ? el : unboundInfinity(oprds.subList(0, os-1));
			case GreaterThan:
			case GreaterEqual: 	
				return oiu ? el : unboundInfinity(oprds.subList(1, os));
			default: 			
			}

		return oprds;
	}
	

	
	protected <OT extends Expression> boolean cacheOperandDirectSideEffect(final OT oprd)
	throws ClassCastException {
		return cacheExpressionalOperandDirectSideEffect(oprd);
	}
	
	protected Proposition andByReduce(Proposition p2) {
		return p2 instanceof OrderRelation 
				? andByReduce((OrderRelation) p2) 
				: null;
	}
	
	private Proposition andByReduce(OrderRelation or2) {
		if (enters(METHOD_AND_BY_REDUCE)) return null;
		
		enter(METHOD_AND_BY_REDUCE);
		final OrderRelation.Operator op = (OrderRelation.Operator) getOp(),
				op2 = (OrderRelation.Operator) or2.getOp();
		
		@SuppressWarnings("unchecked") 
		List<Expression> exps1 = (List<Expression>) toList(), exps2 = (List<Expression>) or2.toList();
		final int lastIndex1 = exps1.size() - 1, lastIndex2 = exps2.size() - 1;
		final VODCondGen sm = getScopeManager();
//		ConditionElement scope = getScope();	// lazy scope setting
		switch (op) {
		case Equal:
			OP2: switch (op2) {
			case NotEqual:
				for (Expression e1 : exps1) if (!exps2.contains(e1)) break OP2;
				return leave(False.from("(A = B && A != B) = F", Proposition.Operator.And, this, or2), 
						METHOD_AND_BY_REDUCE);
				
			case GreaterEqual:
			case GreaterThan:
			case LessEqual:
			case LessThan:
				Expression v = null, nv = null;
				for (Expression e1 : exps1) {
					if (e1 instanceof VariablePlaceholder) v = e1;
					else nv = e1;
				}
				if (v != null && nv != null) {
					ListIterator<Expression> li2 = exps2.listIterator();
					while (li2.hasNext()) if (li2.next().equals(v)) {
						li2.set(nv);
						if (from(op2, exps2).isTrue()) return leave(this, METHOD_AND_BY_REDUCE);
					}
				}
			default:		
				break;
			}
			
		case NotEqual:
			switch (op2) {
			case GreaterEqual:
			case GreaterThan:
			case LessEqual:
			case LessThan:		ignoreDependency(op, or2);
			default:
			}
			
		case GreaterEqual:
		case GreaterThan:
		case LessEqual:
			if (op2.equals(Operator.LessEqual) && lastIndex1 == 1 && lastIndex2 == 1) {
				final Expression domVar = exps1.get(1);
				if (domVar == exps2.get(0)) {
					final Expression lb = exps1.get(0), ub = exps2.get(1);
					if (lb instanceof ArithmeticExpression && ub instanceof ArithmeticExpression) return leave(
							ExpressionRange.from(domVar, (ArithmeticExpression) lb, (ArithmeticExpression) ub), 
							METHOD_AND_BY_REDUCE);
					else DebugElement.throwTodoException("unsupported ranges");
				}
			}
			
		case LessThan:
		default:			
		}

		Proposition result;
		if (!op.equals(op2)) {
			result = or2.andByReduce(this);
			if (result != null) return leave(result, METHOD_AND_BY_REDUCE);

//			if (ignoresDependency(op, or2) || or2.ignoresDependency(op2, this)) 
//				break;
//			for (Expression e1 : exps1) if (or2.dependsOn(e1)) 
//				throwTodoException("unsupported op2?");
		}
		
		// (i) b1 R a /\ a R b2  =  b1 R a R b2
		result = reduceByTransitivity(exps1, lastIndex1, exps2, 0, op, sm);	
		if (result != null) return leave(result, METHOD_AND_BY_REDUCE);
		// (i) b2 R a /\ a R b1  =  b2 R a R b1
		result = reduceByTransitivity(exps2, lastIndex2, exps1, 0, op, sm);
		if (result != null) return leave(result, METHOD_AND_BY_REDUCE);
		// (ii) a R b1 /\ a R b2 /\ b1 R b2  =  a R b1 R b2  =  a R b1
		result = reduceByTransitivity(op,
				this, exps1, 0, lastIndex1, or2, exps2, 0, lastIndex2, sm);
		if (result != null) return leave(result, METHOD_AND_BY_REDUCE);
		// (ii)	b1 R a /\ b2 R a /\ b1 R b2  =  b1 R b2 R a  =  b2 R a
		result = reduceByTransitivity(op,
				this, exps1, lastIndex1, 0, or2, exps2, lastIndex2, 0, sm);
		if (result != null) return leave(result, METHOD_AND_BY_REDUCE);
		return leave((Proposition) null, METHOD_AND_BY_REDUCE);
	}


	
	/**
	 * Converting to {@link Equality} for binary in-equality A != B or n-ary order relation.
	 * 
	 * Converting to {@link OrderRelation} for binary equality A = B.
	 * 
	 * For n-ary set-based order relation (equality and inequality): ~(A1 = A2 = ... = An) 
	 * 	<=> ~(A1 = A2 && A1 = A3 && ... && An-1 = An) 
	 * 	<=> A1 != A2 || A1 != A3 || ... || An-1 != An 
	 * 
	 * For n-ary list-based order relation: ~(A1 R A2 R ... R An) 
	 * 	<=> ~(A1 R A2 && A2 R A3 && ... && An-1 R An) 
	 * 	<=> A1 ~R A2 || A2 ~R A3 || ... || An-1 ~R An 
	 * 
	 * @see ompca.condition.Proposition#notByReduce()
	 */
	protected Proposition notByReduce() {
		Proposition result = null;
		Expression[] orArray = toArray();
		assert orArray != null;
		final Operator op = (Operator) getOp(), nop = (Operator) op.negate();
		final boolean ism = op.isMonotonic();
		for (int l = 0, rMax = orArray.length - 1; l < rMax; l++) {
			if (ism) 
				result = notByOr(nop, orArray[l], orArray[l+1], result);
			else for (int r = l + 1; r <= rMax; r++) 
				result = notByOr(nop, orArray[l], orArray[r], result);
		}
		return result;
	}
	
	private Proposition notByOr(final Operator nop, final Expression l, final Expression r, Proposition result) {
		// Const op Const = T/F	=>	Const nop Const = F/T
//		if (Elemental.tests(()-> l.isConstant() && r.isConstant())) 
//		return result == null 
//			? False.from("l op r = T	=>	l nop r = F", nop, l, r)	// result.or(FALSE) == result 
//			: result;
		
		Supplier<Proposition> lnr = ()-> from(nop, l, r, null);	// can reduce to constant T/F too
		return result == null ? lnr.get() : result.or(lnr);
	}
	
	
	
	/**
	 * For optimization (III)(i):
	 * 	b1 R a /\ a R b2  =  b1 R a R b2
	 * 	b2 R a /\ a R b1  =  b2 R a R b1
	 * 
	 * @param operands1
	 * @param index1
	 * @param operands2
	 * @param index2
	 * @param op 
	 * @param scopeManager 
	 * @return
	 */
	private static OrderRelation reduceByTransitivity(
			List<Expression> operands1, int index1, 
			List<Expression> operands2, int index2, 
			OrderRelation.Operator op, VODCondGen scopeManager) {
		assert 0 <= index1 && index1 < operands1.size() && 
				0 <= index2 && index2 < operands2.size();
		
		try {
			if (operands1.get(index1).equals(operands2.get(index2))) {
				operands2.remove(index2);
				operands1.addAll(operands2);
				// TODO: operands1.scope \/ operands2.scope
				return new OrderRelation(op, operands1, scopeManager);
			}
			
		} catch (IndexOutOfBoundsException e) {
			throwTodoException(e);
		}
		return null;
	}
	
	/**
	 * For optimization (III)(ii):
	 * 	a R b1 /\ a R b2 /\ b1 R b2  =  a R b1 R b2  =  a R b1
	 * 	b1 R a /\ b2 R a /\ b1 R b2  =  b1 R b2 R a  =  b2 R a
	 * 
	 * @param relation1
	 * @param operands1
	 * @param indexA1
	 * @param indexB1
	 * @param relation2
	 * @param operands2
	 * @param indexA2
	 * @param indexB2
	 * @param scopeManager 
	 * @return
	 */
	private static OrderRelation reduceByTransitivity(OrderRelation.Operator op,
			OrderRelation relation1, List<Expression> operands1, int indexA1, int indexB1, 
			OrderRelation relation2, List<Expression> operands2, int indexA2, int indexB2, VODCondGen scopeManager) {
		assert 0 <= indexA1 && indexA1 < operands1.size() && 
				0 <= indexA2 && indexA2 < operands2.size() &&
				0 <= indexB1 && indexB1 < operands1.size() &&
				0 <= indexB2 && indexB2 < operands2.size();
		
		if (operands1.get(indexA1).equals(operands2.get(indexA2)) 
				&& ((indexA1 == 0 && indexA2 == 0) || (indexA1 != 0 && indexA2 != 0))) {
			Expression b1 = operands1.get(indexB1), b2 = operands2.get(indexB2);
			int indexB2in1 = operands1.indexOf(b2), indexB1in2 = operands2.indexOf(b1);
			boolean aRb1 = indexA1 < indexB1;
			if (indexB2in1 != -1) {
				// a R b1 R b2  =  a R b1;	b1 R b2 R a  =  b2 R a
				if (indexB1 < indexB2in1) return aRb1 ? relation1 : relation2;
				// a R b2 R b1  =  a R b2;	b2 R b1 R a  =  b1 R a
				if (indexB2in1 < indexB1) return aRb1 ? relation2 : relation1;
				
			} else if (indexB1in2 != -1) {
				// a R b1 R b2  =  a R b1;	b1 R b2 R a  =  b2 R a
				if (indexB1in2 < indexB2) return aRb1 ? relation1 : relation2;
				// a R b2 R b1  =  a R b2;	b2 R b1 R a  =  b1 R a
				if (indexB2 < indexB1in2) return aRb1 ? relation2 : relation1;
				
			} else {
				Proposition b1Rb2 = OrderRelation.from(op, b1, b2, null),
						b2Rb1 = OrderRelation.from(op, b2, b1, null);
				// a R b1 R b2  =  a R b1;	b1 R b2 R a  =  b2 R a
				if (b1Rb2.isTrue()) return aRb1 ? relation1 : relation2;
				// a R b2 R b1  =  a R b2;	b2 R b1 R a  =  b1 R a
				if (b2Rb1.isTrue()) return aRb1 ? relation2 : relation1;
			}
		}
		
		return null;
	}
	
	
	
	@Override
	protected Expression toConstantIf() {
		return from((Operator) getOp(), toConstantOperands());
	}
	
	
	
	/**
	 * @return non-null
	 */
	@Override
	public String toZ3SmtString(boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs) {
		final Relation.Operator op = getOp();
		final Collection<? extends Expression> nos = getPlatformBoundedOperands();
		return nos.size() <= 1 
				? ""	// T makes parent Or a tautology
//				? True.from(op, toArray()).toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition) 
				: super.toZ3SmtString(op.toZ3SmtString(this, printsVariableDeclaration, printsFunctionDefinition), nos);
		
//		Operator op = (Operator) getOp();
//		boolean isNotEqual = op == Operator.NotEqual;
//		String cond = "(" + (isNotEqual ? "not (=" : op.toZ3SmtString());
//		for (Expression exp : getOperands()) cond += (" " + exp.toZ3SmtString(false, false));
//		return cond + (isNotEqual ? ") )" : ")");
	}

}