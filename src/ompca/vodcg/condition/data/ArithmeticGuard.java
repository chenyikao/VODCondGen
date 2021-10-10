package ompca.vodcg.condition.data;

import java.util.Collection;
import java.util.EnumMap;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

import ompca.Mappable;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.Arithmetic;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.Expression;
import ompca.vodcg.condition.Function;
import ompca.vodcg.condition.Function.Parameter;
import ompca.vodcg.condition.FunctionCall;
import ompca.vodcg.condition.Proposition;
import ompca.vodcg.condition.Relation;

/**
 * A wrapper proposition of {@link Arithmetic}.
 * 
 * @author Kao, Chen-yi
 *
 */
abstract public class ArithmeticGuard 
// extensible for all of unary, binary and n-ary guards
extends Proposition 	
implements NumericExpression {

	public enum Operator implements Relation.Operator {
		Primitive,	// for unary, expression-range guards
		Add, Subtract, Multiply, Divide, Modulo, Max, Min;
		
		/* (non-Javadoc)
		 * @see ompca.vodcg.condition.Relation.Operator#isAssociativeTo(ompca.vodcg.condition.Relation.Operator)
		 */
		@Override
		public boolean isAssociativeTo(Relation.Operator op) {
			return false;
		}
		@Override
		public boolean isCommutative() {
			return Enum.valueOf(Arithmetic.Operator.class, name()).isCommutative();
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
			case Modulo:		
			default:			return null;
			}
		}
		
		public java.lang.String toString() {
			switch (this) {
			case Add:			return "+guard";
			case Subtract:		return "-guard";
			case Multiply:		return "*guard";
			case Divide:		return "/guard";
			case Modulo:		return "%guard";
//			case Remainder:		return "...guard";
			default:
				assert(false); return null;	// should NOT come here!
			}
		}
		
		public <H extends Relation> java.lang.String toZ3SmtString(
				H host, boolean printsVariableDeclaration, boolean printsFunctionDefinition) {
			switch (this) {
			case Add:			return "add_guard";
			case Subtract:		return "sub_guard";
			case Multiply:		return "mul_guard";
			case Divide:		return "div_guard";
			case Modulo:		return "mod_guard";
//			case Remainder:		return "rem_guard";
			default:
				assert(false); return null;	// should NOT come here!
			}
		}
		
	}
	
	
	
//	private final static Method METHOD_FROM = Elemental.getMethod(FiniteIntegerGuard.class, 
//			"from", Arithmetic.class);

	final static private Map<ArithmeticExpression, ArithmeticGuard> 
	GUARD_REGISTRY = new HashMap<>();

	/**
	 * @param arith - arithmetic to guard
	 */
	protected ArithmeticGuard(final Arithmetic arith) {
		super(getOp(arith), arith);
	}
	
	/**
	 * @param unit - arithmetic unit to guard
	 */
	protected ArithmeticGuard(final ArithmeticExpression unit) {
		super(Operator.Primitive, (Expression) unit);
	}
	
	@SuppressWarnings("deprecation")
	protected static ArithmeticGuard from(
			final ArithmeticExpression ae, final Supplier<ArithmeticGuard> gs) {
		assert gs != null;
		if (ae == null) throwNullArgumentException("arithmetic");
		
		ArithmeticGuard g = GUARD_REGISTRY.get(ae);
		if (g == null) try {
			GUARD_REGISTRY.put(ae, g = gs.get());
//			GUARD_REGISTRY.put(ae, g = arith.guardReenter(
//					()-> new FiniteIntegerGuard(arith), ()-> throwStackOverflowException(), METHOD_FROM));
			
		} catch (Exception e) {
			throwUnhandledException(e);
		}
		return g;
	}
	
	public static ArithmeticGuard from(final Arithmetic arith) {
		if (arith == null) throwNullArgumentException("arithmetic");
		return arith.getOp().isBitwise()
				? BitsGuard.from(arith)
				: FiniteNumberGuard.from(arith);
	}
	

	
	private static java.lang.String getName(Arithmetic arith) {
		if (arith == null) throwNullArgumentException("arithmetic");
		return getOp(arith).toZ3SmtString(null, false, false);
	}
	
	private static Relation.Operator getOp(Arithmetic arith) {
		assert arith != null;
//		if (arith.getFirstOperand().getType() != DataType.Int)
//			throwTodoException("non-integer guard");
		
		switch ((Arithmetic.Operator) arith.getOp()) {
		case Add:			return FiniteNumberGuard.Operator.Add;
		case Subtract:		return FiniteNumberGuard.Operator.Subtract;
		case Multiply:		return FiniteNumberGuard.Operator.Multiply;
		case Divide:		
		case IntegerDivide:	return FiniteNumberGuard.Operator.Divide;
		case Modulo:		return FiniteNumberGuard.Operator.Modulo;

		case BitAnd:		return BitsGuard.Operator.BitAnd;
		default:
		}
		return throwTodoException("unsupported arithmetic");
	}
	
	
	
//	@SuppressWarnings("unchecked")
//	@Override
//	public Operator getOp() {
//		final Expression oprd = getFirstRawOperand();
////		if (oprd.isUnary()) return Operator.Primitive;
//		
//		if (oprd instanceof Arithmetic) 
//		switch ((Arithmetic.Operator) ((Arithmetic) oprd).getOp()) {
//		case Add:			return Operator.Add;
//		case Subtract:		return Operator.Subtract;
//		case Divide:
//		case IntegerDivide:	return Operator.Divide;
//		case Max:			return Operator.Max;
//		case Min:			return Operator.Min;
//		case Modulo:		return Operator.Modulo;
//		case Multiply:		return Operator.Multiply;
//		case BitAnd:
//		case ShiftLeft:
//		default:			
//		}
//		return throwTodoException("unsupported op");
//	}
	
	
	
	@Override
	public Collection<? extends Expression> getOperands() {
		final Expression oprd = getFirstRawOperand();
		return oprd instanceof Arithmetic
				? ((Arithmetic) oprd).getOperands()
				: super.getOperands();
	}
	
	/**
	 * One level guarding and no side-effect for the guard.
	 */
	@Override
	protected <OT extends Expression> boolean cacheOperandDirectSideEffect(
			final OT oprd) {
		return false;
	}
	
	/**
	 * One level guarding only - no guards for the guard.
	 */
	@Override
	final protected Set<ArithmeticGuard> cacheArithmeticGuards() {
		return null;
	}
	
	
	
	@Override
	public boolean isGuard() {
		return true;
	}

	
	
	@Override
	public Proposition toProposition() {
		final Arithmetic arith = get(()-> (Arithmetic) getFirstRawOperand(),
				e-> throwTodoException(e));
		final java.lang.String name = getName(arith);
		final List<? extends Expression> args = arith.toList();
		return FunctionCall.from(
				Function.from(VODCondGen.LIB_OMPCA_SMT, 
						name, 
						DataType.Bool, 
						arith.getCondGen(),
						Parameter.from(args)),
				name,
				args,
				arith.getScope()).getCallProposition();
	}
	
	@Override
	public java.lang.String toZ3SmtString(
			boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs) {
		return toProposition().toZ3SmtString(
				printsVariableDeclaration, printsFunctionDefinition, isLhs);
	}
	
}