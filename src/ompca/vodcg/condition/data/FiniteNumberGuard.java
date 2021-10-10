/**
 * 
 */
package ompca.vodcg.condition.data;

import ompca.solver.CarryInRangeDegrader;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.Arithmetic;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.ExpressionRange;
import ompca.vodcg.condition.Function.Parameter;
import ompca.vodcg.condition.Proposition;

/**
 * @author Kao, Chen-yi
 *
 */
public class FiniteNumberGuard extends ArithmeticGuard {

	private static class PositiveGuard extends FiniteNumberGuard {

		/**
		 * @param ae - arithmetic expression to guard
		 */
		private PositiveGuard(ArithmeticExpression ae) {
			super(ae);
		}
		
		@Override
		public Boolean isZero() {
			return false;
		}
		
		@Override
		public Boolean isPositive() {
			return true;
		}
		
		@Override
		public Boolean isNegative() {
			return false;
		}
		
		@Override
		public Proposition toProposition() {
			return ExpressionRange.from(getFirstOperand(), Int.ONE, null);
		}
		
//		@Override
//		public java.lang.String toZ3SmtString(
//				boolean printsVariableDeclaration, boolean printsFunctionDefinition) {
//			final java.lang.String oprd = getFirstOperand().toZ3SmtString(
//					printsVariableDeclaration, printsFunctionDefinition);
//			return "(assert (< 0 " + oprd + ")(<= " + oprd + " " 
//			+ VODCondGen.getPlatformPositiveInfinityInt() + "))\n";
//		}
	}

	private static class NonNegativeGuard extends FiniteNumberGuard {
		
		/**
		 * @param ae - arithmetic expression to guard
		 */
		private NonNegativeGuard(ArithmeticExpression ae) {
			super(ae);
		}
		
		@Override
		public Boolean isZero() {
			return null;
		}
		
		@Override
		public Boolean isPositive() {
			return null;
		}
		
		@Override
		public Boolean isPositiveOrZero() {
			return true;
		}
		
		@Override
		public Boolean isNegative() {
			return false;
		}
		
		@Override
		public Proposition toProposition() {
			return ExpressionRange.from(getFirstOperand(), Int.ZERO, null);
		}
		
//		@Override
//		public java.lang.String toZ3SmtString(
//				boolean printsVariableDeclaration, boolean printsFunctionDefinition) {
//			final java.lang.String oprd = getFirstOperand().toZ3SmtString(
//					printsVariableDeclaration, printsFunctionDefinition);
//			return "(assert (<= 0 " + oprd + ")(<= " + oprd + " " 
//					+ VODCondGen.getPlatformPositiveInfinityInt() + "))\n";
//		}
	}
	

	
	/**
	 * @param ae - arithmetic expression to guard
	 */
	private FiniteNumberGuard(ArithmeticExpression ae) {
		super(ae);
	}
	
	/**
	 * @param arith - arithmetic to guard
	 */
	private FiniteNumberGuard(final Arithmetic arith) {
		super(arith);
	}

	public static FiniteNumberGuard from(final Arithmetic arith) {
		return (FiniteNumberGuard) from(
				arith, ()-> new FiniteNumberGuard(arith));
	}
	
	public static FiniteNumberGuard fromPositive(
			final ArithmeticExpression ae) {
		try {
			return (FiniteNumberGuard) from(
					ae, ()-> new PositiveGuard(ae));
			
		} catch (ClassCastException e) {
			return throwTodoException(e);
		}
	}
	
	public static FiniteNumberGuard fromNonNegative(
			final ArithmeticExpression ae) {
		try {
			return (FiniteNumberGuard) from(
					ae, ()-> new NonNegativeGuard(ae));
			
		} catch (ClassCastException e) {
			return throwTodoException(e);
		}
	}
	


	final public static java.lang.String toZ3SmtDeclaration() {
		final java.lang.String smaxInt = VODCondGen.getSimulatedPositiveInfinityInt(),
				maxInt128 = VODCondGen.getPositiveInfinityInt128(),
				maxInt = VODCondGen.getPlatformPositiveInfinityInt(),
				sminInt = VODCondGen.getPlatformNegativeInfinityInt(),
				maxReal = VODCondGen.getPlatformPositiveInfinityReal(),
				minReal = VODCondGen.getPlatformNegativeInfinityReal(),
				p1 = Parameter.getDefaultName(1),
				p2 = Parameter.getDefaultName(2),
				params = "((" + p1 + " Int)(" + p2 + " Int))";
		return 	"(echo \"Simulating signed 128 bit number domain...\")\n" +
		"(echo \"(including GNU C int128 (2's complement) and IEEE 754 binary128 overflow but excluding underflow)\")\n" +
		"(echo \"(https://gcc.gnu.org/onlinedocs/gcc/Integers-implementation.html#Integers-implementation)\")\n" +
		"(echo \"(https://gcc.gnu.org/onlinedocs/gcc/_005f_005fint128.html#g_t_005f_005fint128)\")\n" +
		"(echo \"(https://en.wikipedia.org/wiki/Quadruple-precision_floating-point_format#IEEE_754_quadruple-precision_binary_floating-point_format:_binary128)\")\n" +
		"(define-fun " + maxInt + " () Int " + maxInt128 + ")  " + CarryInRangeDegrader.getTagMax() + "\n" +
//		"(define-fun " + maxInt + " () Int (bv2int #x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)) " + CarryInRangeDegrader.getTagMax() + "\n" +
//		"(define-fun MAX_MAX_REAL () Real (* (^ 2.0 16383) (- 2.0 (^ 2.0 (- 112))))) ;RangeDegradeMAX\n" +
//		return 	"(echo \"Simulating signed (2's complement) 64 bit number domain...\")\n" +
//		"(echo \"(including C int64 and IEEE 754 binary64 overflow but excluding underflow)\")\n" +
//		"(echo \"(https://en.wikipedia.org/wiki/IEEE_754)\")\n" +
//		"(define-fun " + smaxInt + " () Int (bv2int #x7FFFFFFFFFFFFFFF))\n" +
		"(declare-fun " + smaxInt + " () Int)                  " + CarryInRangeDegrader.getTagParam() + "\n" +
		"(define-fun MIN_MAX_INT () Int 0)                     " + CarryInRangeDegrader.getTagMin() + "\n" +
		"(define-fun " + sminInt + " () Int (- (- " + smaxInt + ") 1))\n" +
		"(define-fun " + maxReal + " () Real (* (^ 2.0 1023) (- 2.0 (^ 2.0 (- 52)))))\n" +
		"(define-fun " + minReal + " () Real (- " + maxReal + "))\n" +
		
				";avoiding +/-/*/division/modulo overflow\n" +
				"(define-fun add_guard " + params + " Bool (and \n" +
				"\t(<= " + sminInt + " _1)(<= _1 " + smaxInt + ")\n" +
				"\t(<= " + sminInt + " _2)(<= _2 " + smaxInt + ")\n" +
				"\t(<= " + sminInt + " (+ _1 _2))(<= (+ _1 _2) " + smaxInt + ")\n" +
				"\t))\n" +
				
				"(define-fun sub_guard " + params + " Bool (and \n" +
				"\t(<= " + sminInt + " _1)(<= _1 " + smaxInt + ")\n" +
				"\t(<= " + sminInt + " _2)(<= _2 " + smaxInt + ")\n" +
				"\t(<= " + sminInt + " (- _1 _2))(<= (- _1 _2) " + smaxInt + ")\n" +
				"))\n" +
				
				"(define-fun mul_guard " + params + " Bool (and \n" +
				"\t(<= " + sminInt + " _1)(<= _1 " + smaxInt + ")\n" +
				"\t(<= " + sminInt + " _2)(<= _2 " + smaxInt + ")\n" +
				"\t(<= " + sminInt + " (* _1 _2))(<= (* _1 _2) " + smaxInt + ")\n" +
				"))\n" +
				
				"(define-fun div_guard " + params + " Bool (and \n" +
				"\t(not (= _2 0))\n" +
				"\t(<= " + sminInt + " " + p1 + ")(<= " + p1 + " " + smaxInt + ")\n" +
				"\t(<= " + sminInt + " _2)(<= _2 " + smaxInt + ")\n" +
				"))\n" +
				
				"(define-fun mod_guard " + params + " Bool (and \n" +
				"\t(div_guard " + p1 + " " + p2 + ")\n" +
				"))";
	}
	
}