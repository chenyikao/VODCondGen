package ompca.vodcg.condition;

import java.lang.reflect.Method;
import java.util.Collection;
import java.util.EnumMap;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import ompca.DuoKeyMultiPartitionMap;
import ompca.DuoKeySetMultiPartitionMap;
import ompca.Elemental;
import ompca.Mappable;
import ompca.MultiPartitionable;
import ompca.vodcg.ASTException;
import ompca.vodcg.ReenterException;
import ompca.vodcg.SystemElement;
import ompca.vodcg.UncertainException;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.data.ArithmeticGuard;
import ompca.vodcg.condition.data.DataType;
import ompca.vodcg.condition.data.Int;
import ompca.vodcg.condition.data.Number;
import ompca.vodcg.condition.data.PlatformType;
import ompca.vodcg.condition.data.Real;

/**
 * Arithmetic	::= ('(' Expression ArithmeticOp Expression ')') | (Expression ArithmeticOp Expression)
 * ArithmeticOp	::= '+'|'-'|'*'|'/'|'%'
 *
 * The root class implementing both {@link SystemElement} and {@link ArithmeticExpression}.
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class Arithmetic extends Relation implements ArithmeticExpression {
	
	final static private 
	DuoKeySetMultiPartitionMap<Expression, Arithmetic, Expression, Expression> 
	ADD_CACHE = new DuoKeySetMultiPartitionMap<>(),
	MULTIPLY_CACHE = new DuoKeySetMultiPartitionMap<>(),
	BIT_AND_CACHE = new DuoKeySetMultiPartitionMap<>();
	
	final static private 
	DuoKeyMultiPartitionMap<Expression, Expression, Arithmetic, Expression, Expression> 
	SHIFT_LEFT_CACHE = new DuoKeyMultiPartitionMap<>(),
	SUBTRACT_CACHE = new DuoKeyMultiPartitionMap<>(),
	DIVIDE_CACHE = new DuoKeyMultiPartitionMap<>(),
	INT_DIVIDE_CACHE = new DuoKeyMultiPartitionMap<>(),
	MODULO_CACHE = new DuoKeyMultiPartitionMap<>();
	
	final static private Map<Operator, 
	DuoKeyMultiPartitionMap<Expression, Expression, Arithmetic, Expression, Expression>> 
	ARITH_CACHE = new EnumMap<>(Operator.class);

	public enum Operator implements Relation.Operator, MultiPartitionable.Key {
		Add, Subtract, Multiply, Divide, IntegerDivide, 
		/**
		 * In computing, the modulo operation finds the remainder or 
		 * signed remainder after division of one number by another 
		 * (called the modulus of the operation).
		 * @see https://en.wikipedia.org/wiki/Modulo_operation
		 */
		Modulo, Max, Min,
		BitAnd, ShiftLeft;

		static public Operator from(String value) {
			if (value == null || value.isEmpty()) return null;
			
			value = value.trim();
			if (value.equals("+")) return Add;
			else if (value.equals("-")) return Subtract;
			else return null;	// TODO
		}
		
		/* (non-Javadoc)
		 * @see ompca.vodcg.condition.Relation.Operator#isAssociativeTo(ompca.vodcg.condition.Relation.Operator)
		 */
		@Override
		public boolean isAssociativeTo(Relation.Operator op) {
			switch (this) {
			case Add:			
			case Subtract:		return op == Add || op == Subtract;
			case Multiply:		
			case Divide:		return op == Multiply || op == Divide;
			default:			return false;
			}
		}

		@Override
		public boolean isCommutative() {
			switch (this) {
			case Add:			
			case BitAnd:			
			case Multiply:		return true;
			default:			return false;
			}
		}
		
		@Override
		public boolean isBitwise() {
			switch (this) {
			case BitAnd:			
			case ShiftLeft:		return true;
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
		 * @see ompca.vodcg.condition.Relation.Operator#negate()
		 */
		@Override
		public ompca.vodcg.condition.Relation.Operator negate() {
			switch (this) {
			case Add:			return Subtract;
			case Subtract:		return Add;
			case Multiply:		return Divide;
			case Divide:		return Multiply;
			default:			return null;
			}
		}

		public String toString() {
			switch (this) {
			case Add:			return "+";
			case Subtract:		return "-";
			case Multiply:		return "*";
			case Divide:
			case IntegerDivide:	return "/";
			case Modulo:		return "%";
//			case Remainder:		return "...";
			case BitAnd:		return "&";
			case ShiftLeft:		return "<<";
			default:			return "(unsupported)";	
			}
		}
		
		public <H extends Relation> String toZ3SmtString(
				H host, boolean printsVariableDeclaration, boolean printsFunctionDefinition) {
			switch (this) {
			case Add:			return "+";
			case Subtract:		return "-";
			case Multiply:		return "*";
			case Divide:		return "/";
			case IntegerDivide:	return "div";
			case Modulo:		return "mod";
//			case Remainder:		return "rem";
			case BitAnd:		return "bvand";
			default:			return "unsupported?";	
			}
		}

	}


	
	private static final Method 
	METHOD_FROM = Elemental.getMethod(Arithmetic.class, "from", 
			Operator.class, ArithmeticExpression.class, ArithmeticExpression.class),
	METHOD_FROM_2 = Elemental.getMethod(Arithmetic.class, "from", 
			Operator.class, Expression.class, Expression.class),
	METHOD_IS_ZERO = Elemental.getMethod(Arithmetic.class, "isZero"),
	METHOD_IS_POSITIVE = Elemental.getMethod(Arithmetic.class, "isPositive"),
	METHOD_IS_INFINITY = Elemental.getMethod(Arithmetic.class, "isInfinity", 
			boolean.class),
	METHOD_IS_LESS_THAN = Elemental.getMethod(Arithmetic.class, "isLessThan", 
			Arithmetic.class);

	private boolean resetsIsZero = true;	// caching flag per operation
	private Boolean isZero;					// for caching and isZero()-equals() performance
	
//	private ArrayList<Expression> operandList;

//	/**
//	 * Constant unary arithmetic (e.g. {@link Number}) constructor.
//	 * 
//	 * @param condGen 
//	 */
//	protected Arithmetic(VODCondGen condGen) {
//		super(Operator.Add, condGen);
//		
////		operandList.add(Int.ONE);
////		super.add(this);
//		init(true);
//	}
	
	private Arithmetic(
			Operator op, Expression leftOperand, Expression rightOperand) {
		super(op, leftOperand, rightOperand);

		init(get(()-> 
		leftOperand.isConstant() && rightOperand.isConstant(), e-> null));
	}
	
	/**
	 * Unary arithmetic constructor.
	 * 
	 * @param op
	 * @param operand
	 */
	private Arithmetic(Operator op, Expression operand) {
		super(op, operand);

		if (op.equals(Operator.Add)) throwTodoException("op is reduceable");
		
		final Boolean oic = operand.isConstant();
		if (!tests(oic)) setScope(()-> operand.getScope());
		init(oic);
	}
	
//	/**
//	 * N-ary arithmetic constructor.
//	 * 
//	 * @param op
//	 * @param operands - assumed non-empty.
//	 */
//	private Arithmetic(Operator op, List<? extends Expression> operands) {
//		super(op, operands, ()-> new ArrayList<>());
//		
//		assert operands != null && !operands.isEmpty();
//		for (Expression oprd : operands) {
//			if (oprd == null) throwNullArgumentException("operand");
//			final Boolean oic = oprd.isConstant();
//			if (oic == null || !oic) {init(oic); return;}
//		}
//		init(true);
//	}
	
	/**
	 * Inserting guard as side-effect.
	 * @param isConst
	 */
	private void init(final Boolean isConst) {
		setConstant(isConst);
		if (isConst == null || !isConst) {	// means there're true variables
			for (Expression e : getOperands()) 
				if (!VODCondGen.isBounded(e.getType())) return;
			addGuard(ArithmeticGuard.from(this));
		}
	}
	
	private static Expression cache(
			DuoKeyMultiPartitionMap<Expression,Expression,Arithmetic,Expression,Expression> cache, 
			Expression lhs, Expression rhs, Expression a) {
		assert lhs != null && rhs != null && a != null;
		// caching first to avoid circular construction and hence stack overflow
		cache.put(lhs, rhs, a);
		
		try {
			if (a.toString().matches("(\\(0\\)*\\(0\\))|(\\(1\\)*\\(1\\))")) throwReductionException();
//		if (a instanceof Relation && a instanceof ArithmeticExpression) {
//			final Number<?> ZERO = ((ArithmeticExpression) a).getZero();
//			if (lhs instanceof Relation && ((Relation) lhs).contains(ZERO) 
//					&& rhs instanceof Relation && ((Relation) rhs).contains(ZERO)) throwReductionException();
//			final Number<?> ONE = ((ArithmeticExpression) a).getZero();
//			if (lhs instanceof Relation && ((Relation) lhs).contains(ZERO) 
//					&& rhs instanceof Relation && ((Relation) rhs).contains(ZERO)) throwReductionException();
//		}
		} catch (Exception e) {
			throwTodoException(e);
		}
		
		return a;
	}
	
	/**
	 * Non-assignments have NO side-effects of their own to propagate outwards.
	 * 
	 * @param exp - to be checked if it's a non-assignment
	 * @param expOp
	 * @param operand
	 * @param scope
	 * @return
	 */
	public static Arithmetic from(IASTUnaryExpression exp, int expOp, Expression operand) {
		
		Operator op = null;
		switch (expOp) {
		case IASTUnaryExpression.op_minus:		op = Operator.Subtract; break;
		case IASTUnaryExpression.op_plus:		op = Operator.Add; break;
		}
		
		return (op != null) ? new Arithmetic(op, operand) : null;
	}
	
	/**
	 * Non-assignments have NO side-effects of their own to propagate outwards.
	 * 
	 * @param expOp - to be checked if it's a non-assignment
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	public static Expression from(int expOp, Expression lhs, Expression rhs) {
		if (lhs == null) throwNullArgumentException("lhs!");
		if (rhs == null) throwNullArgumentException("rhs!");
		
		Operator op = null;
		switch (expOp) {
		case IASTBinaryExpression.op_divide:	op = Operator.Divide; 	break;
		case IASTBinaryExpression.op_max:		op = Operator.Max; 		break;
		case IASTBinaryExpression.op_min:		op = Operator.Min; 		break;
		case IASTBinaryExpression.op_minus:		op = Operator.Subtract; break;
		case IASTBinaryExpression.op_modulo:	op = Operator.Modulo; 	break;
		case IASTBinaryExpression.op_multiply:	op = Operator.Multiply; break;
		case IASTBinaryExpression.op_plus:		op = Operator.Add; 		break;
		
		// Todo? op = Bitvector.Operator.ShiftLeft or reduced by lhs * 2^rhs 
		case IASTBinaryExpression.op_shiftLeft: op = Operator.ShiftLeft;break;
		case IASTBinaryExpression.op_binaryAnd: op = Operator.BitAnd;	break;
		case IASTBinaryExpression.op_shiftRight:throwTodoException("op = Bitvector.Operator.ShiftRight"); break;
		}
		
		return op == null ? null : from(op, lhs, rhs); 
	}

	public static Expression from(Operator op, Expression lhs, Expression rhs) 
			throws ASTException, UncertainException {
		if (op == null) throwNullArgumentException("operator");
		if (lhs == null) throwNullArgumentException("lhs");
		if (rhs == null) throwNullArgumentException("rhs");
		
		lhs = (Expression) lhs.reduce(METHOD_FROM);
		rhs = (Expression) rhs.reduce(METHOD_FROM);
		
		// cached lhs and rhs
		if (ARITH_CACHE.isEmpty()) {
			ARITH_CACHE.put(Operator.Add,			ADD_CACHE);
			ARITH_CACHE.put(Operator.Subtract,		SUBTRACT_CACHE);
			ARITH_CACHE.put(Operator.Multiply,		MULTIPLY_CACHE);
			ARITH_CACHE.put(Operator.ShiftLeft,		SHIFT_LEFT_CACHE);
			ARITH_CACHE.put(Operator.Divide,		DIVIDE_CACHE);
			ARITH_CACHE.put(Operator.IntegerDivide,	INT_DIVIDE_CACHE);
			ARITH_CACHE.put(Operator.Modulo,		MODULO_CACHE);
			ARITH_CACHE.put(Operator.BitAnd,		BIT_AND_CACHE);
		}
		final DuoKeyMultiPartitionMap<Expression,Expression,Arithmetic,Expression,Expression> 
		opCache = ARITH_CACHE.get(op);
		if (opCache == null) throwTodoException("unsupported op");
		Expression a = opCache.get(lhs, rhs);
		if (a != null) return a;

		// ArithmeticExpression lhs and rhs
		if (rhs instanceof ArithmeticExpression && lhs instanceof ArithmeticExpression) try {
			/* rhs needs to guard since Arithmetic.from(...) is never called twice by 
			 * getZero().add(rhs) even for different rhs's. 
			 */
			if (lhs.enters(METHOD_FROM) && rhs.enters(METHOD_FROM)) {
				lhs.leave(METHOD_FROM);
				rhs.throwReenterException(METHOD_FROM);
			}
			lhs.enter(METHOD_FROM); rhs.enter(METHOD_FROM);
			a = (Expression) ArithmeticExpression.from(
					op, (ArithmeticExpression) lhs, (ArithmeticExpression) rhs);
			lhs.leave(METHOD_FROM); rhs.leave(METHOD_FROM);
			
		} catch (ReenterException e) {	// reentering METHOD_FROM
			e.leave(METHOD_FROM);
		} catch (ClassCastException e) {
			return throwTodoException("unsupported arithemetics?", e);
		}
		if (a != null) return cache(opCache, lhs, rhs, a);
		
		// Arithmetic lhs and rhs
		final PlatformType type = lhs.getType();	// TODO: type-checking both lhs and rhs Expression's
		final Number<?> ZERO = type.equals(DataType.Real) ? Real.ZERO : Int.ZERO, 
				ONE = type.equals(DataType.Real) ? Real.ONE : Int.ONE;
		if (rhs instanceof Arithmetic && lhs instanceof Arithmetic) 
			a = from(op, (Arithmetic) lhs, (Arithmetic) rhs, ZERO, ONE); 
		if (a != null) return cache(opCache, lhs, rhs, a);

		final boolean ler = lhs.equals(rhs);
		switch (op) {
		case Add:
			// ? + -? = 0
			if (lhs.equals(rhs.minus())) return cache(opCache, lhs, rhs, ZERO);
			break;
			
		case Subtract:
			// ? - ? = 0
			if (ler) return cache(opCache, lhs, rhs, ZERO);
			break;
			
		case Divide:
		case IntegerDivide:
			// ? / ? = 1
			if (ler) return cache(opCache, lhs, rhs, ONE);
			break;
			
		case Max:
			break;
		case Min:
			break;
		case Modulo:
			break;
			
		default: break;
		}

		if (lhs.enters(METHOD_FROM_2) && rhs.enters(METHOD_FROM_2)) 
			lhs.throwTodoException(null, METHOD_FROM_2);
		lhs.enter(METHOD_FROM_2); rhs.enter(METHOD_FROM_2);
		a = new Arithmetic(op, lhs, rhs);
		lhs.leave(METHOD_FROM_2); rhs.leave(METHOD_FROM_2);
		return cache(opCache, lhs, rhs, a);
	}
	
	public static Arithmetic from(Operator op, Expression operand) {
		if (op == null) throwNullArgumentException("operator");
		switch (op) {
		case Add: 
		case Subtract: return new Arithmetic(op, operand);
		default:
		}
		
		throwTodoException("Unary arithmetic for '" + op + "'!");
		return null;
	}
	
	public static Expression from(Operator op, List<? extends Expression> operands) {
		if (op == null) throwNullArgumentException("operator");
		if (operands == null || operands.isEmpty()) throwNullArgumentException("operands");
		
		Expression result = operands.get(0);
		final int size = operands.size();
		// unary arithmetic is default to identity except negation
		if (size == 1) return op == Operator.Subtract 
					? from(op, result)
					: result;	

		// optimization by divide-and-conquer
		for (Expression oprd : operands.subList(1, size)) 
			result = from(op, result, oprd);
		return result;
	}
	
	public static ArithmeticExpression from(
			Operator op, ArithmeticExpression lhs, ArithmeticExpression rhs) 
					throws UncertainException {
		try {
			return (ArithmeticExpression) from(
					op, (Expression) lhs, (Expression) rhs);
			
		} catch (ClassCastException e) {
			return throwTodoException("unsupported arithemetics?", e);
		}
	}
	
	/**
	 * Optimizing (flattening) hierarchical addition operands.
	 * @param op
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	@SuppressWarnings("unchecked")
	private static Expression from(Operator op, Arithmetic lhs, Arithmetic rhs, 
			final Number<?> ZERO, final Number<?> ONE) {
		assert op != null && lhs != null && rhs != null;
		
		final Relation.Operator lOp = lhs.getOp(), rOp = rhs.getOp();
		switch (op) {
		case Add:
			// (+ ...) + (+ ...) = lhs.addAll(rhs)
			if (op.equals(lOp) && op.equals(rOp)) {
				List<Expression> es = (List<Expression>) lhs.toList();
				es.addAll((Collection<? extends Expression>) rhs.getOperands());
				if (!es.isEmpty()) return es.size() == 1 ?
						from(op, es.get(0)) : from(op, es);
			}
			// (- ... x) + (+ ... x) = (- ...) + (+ ...)
			if ((lOp == Operator.Subtract && rOp == Operator.Add) 
					|| (rOp == Operator.Subtract && lOp == Operator.Add)) 
				return reduceByIdentity(op, lOp, (List<Expression>) lhs.toList(), 
							rOp, (List<Expression>) rhs.toList(), ZERO);
			break;	// general new Arithmetic(...)
			
		case Subtract:
			// (+ ... x) - (+ ... x) = (+ ...) - (+ ...)
			if (lOp == Operator.Add && rOp == Operator.Add) return reduceByIdentity(
					op, lOp, (List<Expression>) lhs.toList(), 
					rOp, (List<Expression>) rhs.toList(), ZERO);
			// TODO: (- ...) - (+ ...) = lhs.addAll(rhs)
			// TODO: (- ...) - ? = lhs.add(rhs)
			break;	// general new Arithmetic(...)
			
		case ShiftLeft:
			// TODO? A << 1 = A * 2
//			if (Elemental.tests(rhs.equals(ONE))) return lhs;
			break;	// general new Arithmetic(...)
			
		case Multiply:
			// 1 * A = A * 1 = A
			if (Elemental.tests(lhs.equals(ONE))) return rhs;
			if (Elemental.tests(rhs.equals(ONE))) return lhs;
			// TODO: (* ...) * ? = lhs.add(rhs)
			// TODO: (* ...) * (* ...) = lhs.addAll(rhs)
			break;	// general new Arithmetic(...)
			
		case Divide:
		case IntegerDivide:
			// TODO: (/ ...) / (* ...) = lhs.addAll(rhs)
			// A / 1 = A
			if (Elemental.tests(rhs.equals(ONE))) return lhs;
			break;	// general new Arithmetic(...)
			
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
			throwTodoException(lhs.toString() + op.toString() + rhs.toString());
			break;
		}
		
		return null;
	}


	
	/**
	 * TODO: type-checking
	 * all Int operands -> Int
	 * all Real operands -> Real
	 * all Int/Real operands -> Real
	 * 
	 * @see ompca.vodcg.condition.Expression#getType()
	 */
	@Override
	public PlatformType getType() {
		for (Expression e : getOperands()) return e.getType();
		return null;
	}


	
	/**
	 * Resetting children properties, such as isZero flag.
	 */
	protected void setDirty() {
		resetsIsZero = true;
		super.setDirty();
	}


	
	/**
	 * @param iz
	 * @return
	 */
	private Boolean setIsZero(Boolean iz) {
		isZero = iz;
		resetsIsZero = false;
		return isZero;
	}
	
	@Override
	public Boolean isZero() 
			throws ASTException {
		if (!resetsIsZero) return isZero;
		
		SystemElement r = reduce(METHOD_IS_ZERO);
		if (r != this && r instanceof ArithmeticExpression) 
			return setIsZero(((ArithmeticExpression) r).isZero());

		final List<? extends Expression> operands = toList();
		if (operands.isEmpty()) return setIsZero(null);
		
		assert getOp() instanceof Operator;
		final int oSize = operands.size();
		final Operator op = (Operator) getOp();
		final Expression o0 = operands.get(0),
				oRest = oSize > 1 && (op == Operator.Add || op == Operator.Subtract) ?
						from(Operator.Add, operands.subList(1, oSize)) : null;
		try {
		final Boolean iz = ((ArithmeticExpression) o0).isZero();
		switch (op) {
		
		case Add: try {
			return setIsZero(oRest == null ? iz : o0.equals(oRest.minus()));
		} catch (Exception e) {
			return setIsZero(oRest.equals(o0.minus()));
		}

		case Subtract: 	
			return setIsZero(oRest == null ? iz : o0.equals(oRest));
			
		case Multiply:
			if (!iz) for (Expression e : operands) 
				if (((ArithmeticExpression) e).isZero()) return setIsZero(true); 
			return setIsZero(false);
			
		case Divide:
		case IntegerDivide: 
		case Modulo:		
		case ShiftLeft:		
			return setIsZero(iz);
			
		case Max:
		case Min:
		default:
			throwTodoException("Unsupported isZero()!");
		}} catch (ASTException e) {
			throw e;
		} catch (NullPointerException | ClassCastException e) {
			return setIsZero(null);
		} catch (Exception e) {
			throwUnhandledException(e);
		}
		
		return ArithmeticExpression.super.isZero();
	}
	
	@Override
	public Boolean isPositive() {
		SystemElement r = reduce(METHOD_IS_POSITIVE);
		if (r != this && r instanceof ArithmeticExpression) 
			return ((ArithmeticExpression) r).isPositive();

		List<? extends Expression> operands = toList();
		if (operands.isEmpty()) return null;
		
		try {
		final ArithmeticExpression e0 = 
				(ArithmeticExpression) operands.get(0);
		Boolean isP = getSkipNull(()-> e0 != this && e0.isPositive());
		operands = operands.subList(1, operands.size());
		switch ((Operator) getOp()) {
		case Add: 
			for (Expression e : operands) {
				if (e == this) continue;
				ArithmeticExpression ae = (ArithmeticExpression) e;
				if (ae.isPositive()) {if (!isP) return null;}	// (-) + (+)
				else if (isP) return null;						// (+) + (-) 
			}
			return isP;

		case Subtract:
			return operands.isEmpty() 
					? !isP 
					: ((ArithmeticExpression) from(Operator.Add, operands)).isLessThan(e0);
		
		case Multiply:
		case Divide:
		case IntegerDivide:
		case BitAnd:
			for (Expression e : operands) {
				if (e == this) continue;
				Boolean isEP = ((ArithmeticExpression) e).isPositive();
				if (!isP && !isEP) isP = true;
				else isP &= isEP;
			}
			return isP;
			
		case ShiftLeft:
			// TODO: return e0.toBits().shiftLeft(e1).isP;
			return isP;
		
		case Modulo:
			return null;
			
		case Max:
		case Min:
		default:
			throwTodoException("isPositive()? " + toString());
		}
		
//		boolean existsA1 = false, existsInt = false;
//		for (Expression a2e : a2.getOperands()) {
//			boolean isA1 = equals(a2e);
//			existsA1 |= isA1;
//			existsInt &= a2e instanceof Int || isA1; 
//		}
//		return existsA1 && ;
		} catch (NullPointerException e1) {
			return null;
		} catch (ClassCastException e2) {
			throwUnhandledException(e2);
		}
		
		return ArithmeticExpression.super.isPositive();
	}
	
	@Override
	public Boolean isPositiveOrZero() {
		SystemElement r = reduce(METHOD_IS_POSITIVE);
		if (r != this && r instanceof ArithmeticExpression) 
			return ((ArithmeticExpression) r).isPositive();
		
		List<? extends Expression> operands = toList();
		if (operands.isEmpty()) return ArithmeticExpression.super.isPositiveOrZero();
		
		try {
			final ArithmeticExpression e0 = 
					(ArithmeticExpression) operands.get(0);
			Boolean isPZ = getSkipNull(()-> e0 != this && e0.isPositiveOrZero());
			operands = operands.subList(1, operands.size());
			switch ((Operator) getOp()) {
//			case Add: 
//				for (Expression e : operands) {
//					if (e == this) continue;
//					ArithmeticExpression ae = (ArithmeticExpression) e;
//					if (ae.isPositive()) {if (!isP) return null;}	// (-) + (+)
//					else if (isP) return null;						// (+) + (-) 
//				}
//				return isP;
//				
//			case Subtract:
//				return operands.isEmpty() 
//						? !isP 
//						: ((ArithmeticExpression) from(Operator.Add, operands)).isLessThan(e0);
//				
//			case Multiply:
//			case Divide:
//			case IntegerDivide:
//			case BitAnd:

			/** The sign of the result for modulo operator is 
			 * machine-dependent for negative operands 
			 * @see https://www.geeksforgeeks.org/modulo-operator-in-c-cpp-with-examples/
			 */
			case Modulo:
				for (Expression e : operands) {
					if (e == this) continue;
					Boolean isEPZ = 
							((ArithmeticExpression) e).isPositiveOrZero();
//					if (!isPZ && !isEPZ) isPZ = true;
					isPZ &= isEPZ;
				}
				return isPZ;
				
//			case ShiftLeft:
//				// TODO: return e0.toBits().shiftLeft(e1).isP;
//				return isP;
				
//			case Max:
//			case Min:
			default:
//				return throwTodoException("isPositiveOrZero()? " + toString());
			}
			
		} catch (NullPointerException e1) {
			return null;
		} catch (ClassCastException e2) {
			throwUnhandledException(e2);
		}
		
		return ArithmeticExpression.super.isPositiveOrZero();
	}
	
	@Override
	public Boolean isPositiveInfinity() {
		return isInfinity(true);
	}
	
	@Override
	public Boolean isNegative() {
		try {
			return testsSkipNull(()->
			isUnaryNegative() || ArithmeticExpression.super.isNegative());
			
		} catch (ReenterException e) {
			e.leave();
			return null;
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	
	@Override
	public Boolean isNegativeInfinity() {
		return isInfinity(false);
	}
	
	public boolean isUnaryNegative() {
		return isUnary() && getOp().equals(Operator.Subtract);
	}
	
	public Boolean isInfinity(final boolean isPositive) {
		final Operator op = (Operator) getOp();
		if (op.isBitwise()) return false;
		
		if (enters(METHOD_IS_INFINITY)) return null;
		
		SystemElement r = reduce(METHOD_IS_INFINITY);
		if (r != this && r instanceof ArithmeticExpression) {
			final ArithmeticExpression a = (ArithmeticExpression) r;
			return isPositive ? a.isPositiveInfinity() : a.isNegativeInfinity();
		}
		
		List<? extends Expression> operands = toList();
		if (operands.isEmpty()) return null;
		try {
			final ArithmeticExpression e0 = (ArithmeticExpression) operands.get(0);
			if (e0 == this) throwInvalidityException("circular dependency");
			
			enter(METHOD_IS_INFINITY);
			Boolean hasPI = e0.isPositiveInfinity(), hasNI = e0.isNegativeInfinity();
			operands = operands.subList(1, operands.size());
			boolean checksBinaryInfinity = false;
			switch (op) {
			
			case Add:
				for (Expression e : operands) {
					if (e == this) continue;
					final ArithmeticExpression ae = (ArithmeticExpression) e;
					if (tests(ae.isPositiveInfinity())) {
						hasPI = !tests(hasNI);	// -oo + oo = 0, x + oo = oo
						hasNI = false;
					}
					else if (tests(ae.isNegativeInfinity())) {
						hasNI = !tests(hasPI);	// oo + -oo = 0, x + -oo = -oo
						hasPI = false;
					}
				}
				break;
				
			case Subtract:		
				for (Expression e : operands) {
					if (e == this) continue;
					final ArithmeticExpression ae = (ArithmeticExpression) e;
					if (tests(ae.isPositiveInfinity())) {
						hasNI = !tests(hasPI);	// oo - oo = 0, x - oo = -oo
						hasPI = false;
					}
					else if (tests(ae.isNegativeInfinity())) {
						hasPI = !tests(hasNI);	// -oo - -oo = 0, x - -oo = oo
						hasNI = false;
					}
				}
				break;
				
			case Multiply:
				if (tests(e0.isZero())) return false;		// 0 * x = 0
				for (Expression e : operands) {
					if (e == this) continue;
					final ArithmeticExpression ae = (ArithmeticExpression) e;
					if (tests(ae.isZero())) {hasPI = hasNI = false; break;}	// x * 0 = 0
					// oo * oo = oo, x * oo = oo, -oo * oo = -oo, -x * oo = -oo
					// oo * -x = -oo, -oo * -x = oo
					// oo * x = oo, -oo * x = -oo
					else if (tests(ae.isPositiveInfinity())) hasPI = true;	
					else if (tests(ae.isNegativeInfinity())) hasNI = true;	
				}
				checksBinaryInfinity = true;
				break;
				
//			case ShiftLeft:
//				if (tests(e0.isZero())) return false;		// 0 << x = 0
//				for (Expression e : operands) {
//					if (e == this) continue;
//					final ArithmeticExpression ae = (ArithmeticExpression) e;
//					if (tests(ae.isZero())) break;		// x << 0 = x
//					// TODO: oo << oo = oo, x << oo = oo, -oo << oo = -oo, -x << oo = -oo
//					// oo << -x = oo, -oo << -x = -oo
//					// oo << x = oo, -oo << x = -oo
////					else if (Elemental.tests(ae.isPositiveInfinity())) hasPI = true;	
////					else if (Elemental.tests(ae.isNegativeInfinity())) hasNI = true;	
//				}
//				checksBinaryInfinity = true;
//				break;
				
			case Divide:
			case IntegerDivide:	
			case Modulo:
				if (tests(e0.isZero())) return false;		// 0 / x = 0
				for (Expression e : operands) {
					if (e == this) continue;
					final ArithmeticExpression ae = (ArithmeticExpression) e;
					if (tests(ae.isZero())) throwTodoException("divide by zero");	// x / 0 = ?
					// oo / x = oo, oo / -x = -oo
					// -oo / x = -oo, -oo / -x = oo
					// x / oo -> 0, oo / oo = 1, -oo / oo = -1, -oo / oo = -1, -oo / -oo = 1
					else if (tests(()-> ae.isPositiveInfinity() || ae.isNegativeInfinity())) return false;	
				}
				checksBinaryInfinity = true;
				break;
				
			case Max:
			case Min:
			default:
				throwTodoException("is infinity? " + toString());
			}
			leave(METHOD_IS_INFINITY);
			
			if (checksBinaryInfinity) if (tests(hasPI) || tests(hasNI)) {
				if (tests(isPositive())) {hasPI = true; hasNI = false;} 
				else if (tests(isNegative())) {hasPI = false; hasNI = true;} 
			}
			if (hasPI != null && isPositive) return hasPI;	
			if (hasNI != null && !isPositive) return hasNI;	
			
		} catch (NullPointerException e1) {
		} catch (ClassCastException e2) {
			throwTodoException(e2);
//			throwTodoException("unsupported arithmetic expression: " + toString());
		}
		
		return guard(()-> isPositive 
				? ArithmeticExpression.super.isPositiveInfinity()
				: ArithmeticExpression.super.isNegativeInfinity(),
				()-> null,
				e-> throwTodoException(e),
				METHOD_IS_INFINITY);
	}
	
//	@Override
//	public Boolean isLessThan(ArithmeticExpression e2) {
//		if (e2 == null) return null;
//		if (e2 instanceof Arithmetic) return isLessThan((Arithmetic) e2);
//		return super.isLessThan(e2);
//	}
	
	/**
	 * The root implementation for {@link SystemElement} reduction within  
	 * {@link ArithmeticExpression} operations.
	 * 
	 * TODO:
	 * a1 < a1 + (positive Int)
	 * a1 < a1 - (negative Int)
	 * a1 < a1 * (positive Int)
	 * a1 < max(an) if exists an s.t. a1 < an
	 * a1 < min(an) if forall an s.t. a1 < an
	 * ...
	 * 
	 * @param a2
	 * @return null when the result is unknown.
	 */
	public Boolean isLessThan(Arithmetic a2) {
		if (a2 == null) return null;
		
		SystemElement r1 = reduce(METHOD_IS_LESS_THAN), r2 = a2.reduce(METHOD_IS_LESS_THAN);
		if (r1 != this || r2 != a2) {
			if (r1 instanceof ArithmeticExpression && r2 instanceof ArithmeticExpression) 
				return ((ArithmeticExpression) r1).isLessThan((ArithmeticExpression) r2);
			else 
				throwTodoException("Unsupported reduced type!");
		}
		return isLessThan((ArithmeticExpression) a2);
	}

	
	
	@Override
	final public boolean containsArithmetic() {
		return true;
	}

	

//	@Override
//	public Boolean equalsLogically(NumericExpression ne2) {
//		return equals((Object) ne2) ? true : null;
//	}
	
	
	
//	final private static Method METHOD_EXPRESSION_TRAVERSAL = 
//			getMethod(Arithmetic.class, "initiatesExpressionTraversal");
//	/* (non-Javadoc)
//	 * @see ompca.vodcg.condition.ArithmeticExpression#initiatesExpressionTraversal()
//	 */
//	@Override
//	public boolean initiatesExpressionComputation() {
//		return initiatesElementalTraversal(METHOD_EXPRESSION_TRAVERSAL);
//	}
//
//	/* (non-Javadoc)
//	 * @see ompca.vodcg.condition.ArithmeticExpression#initiateExpressionTraversal()
//	 */
//	@Override
//	public void initiateExpressionComputation() {
//		initiateElementalTraversal(METHOD_EXPRESSION_TRAVERSAL);
//	}
//
//	/* (non-Javadoc)
//	 * @see ompca.vodcg.condition.ArithmeticExpression#resetExpressionTraversal()
//	 */
//	@Override
//	public void resetExpressionComputation() {
//		resetElementalTraversal(METHOD_EXPRESSION_TRAVERSAL);
//	}
	
	
	
	/**
	 * @see ompca.vodcg.condition.Relation#reduceOnce()
	 */
	public Expression reduceOnce() {
		if (getOp().equals(Operator.Add) && hasOnlyOperand()) 
			return getFirstOperand();
		
		super.reduceOnce();
		return this;
	}

	private static Expression reduceByIdentity(Operator op, 
			Relation.Operator lOp, List<Expression> lhs, 
			Relation.Operator rOp, List<Expression> rhs, Number<?> ZERO) {
		ListIterator<Expression> lit = lhs.listIterator();
		while (lit.hasNext()) {
			ListIterator<Expression> rit = rhs.listIterator();
			Expression le = lit.next();
			while (rit.hasNext()) {
				Expression re = rit.next();
				if (le.equals(re)) try {
					lit.remove(); if (lhs.isEmpty()) lit.add(ZERO);
					rit.remove(); if (rhs.isEmpty()) rit.add(ZERO);
					return from(op, from((Operator) lOp, lhs), from((Operator) rOp, rhs));
				} catch (UnsupportedOperationException ex) {
					throwTodoException(ex.toString());
				}
			}
		}
//		VOPCondGen.throwTodoException("Lists have no identities?");
		return null;
	}


	
//	@Override
//	public Expression rest(Expression e) {
//		return super.rest(e).reduceOnce();
//	}

	
	
	@Override
	public Expression negate() throws ASTException {
		final List<? extends Expression> operands = toList();
		assert !operands.isEmpty();
		try {
		final Expression o0 = operands.get(0), o0minus = o0.minus();
		final List<? extends Expression> oRest = 
				operands.subList(1, operands.size());
		final boolean isUnary = oRest.isEmpty();

		final Operator op = (Operator) getOp();
		assert op != null;
		switch (op) {
		
		case Add:
			// - (A + B) = (-A) - B
			return isUnary 
					? o0minus 
					: from(Operator.Subtract, o0minus, from(op, oRest));

		case Subtract:
			// - (A - B) = (-A) + B
			return isUnary 
					? o0 
					: from(Operator.Add, o0minus, from(op, oRest));
//			if (isUnaryNegative()) return getFirstOperand();

		case Multiply:
		case Divide:
		case IntegerDivide:
			// - (A * B) = (-A) * B, - (A / B) = (-A) / B
			return from(op, o0minus, from(op, oRest));
		
		case Max:
		case Min:
		default:
			break;
		}
		
		throwTodoException("-" + toString());
		return (Expression) getZero().subtract(this);
		} catch (ASTException e) {
			throw e;
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	


	protected Expression toConstantIf() {
		if (isUnaryNegative()) return getFirstOperand().negate();
		
		final List<? extends Expression> cos = (List<? extends Expression>) toConstantOperands();
		return cos.equals(getOperands()) ? this : from((Operator) getOp(), cos);
	}


	
	protected String toNonEmptyString(boolean usesParenthesesAlready) {
//		String uc = debugCallDepth(()-> toNonEmptyString());
		final String uc = Elemental.tests(isConstant()) || isUnary() ? toNonEmptyString() : null;
		return uc == null ? 
				super.toNonEmptyString(usesParenthesesAlready) : uc;
	}
	
}