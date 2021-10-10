package ompca.vodcg.condition.data;

import java.lang.String;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

import ompca.vodcg.SystemElement;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.Expression;

/**
 * @author Kao, Chen-yi
 *
 */
public class Real extends Number<BigDecimal> {

	private static final Map<BigDecimal, Real> REAL_CACHE = new HashMap<>();
	
	public static final Real ZERO = 		from(BigDecimal.ZERO, null);
	public static final Real ONE = 			from(BigDecimal.ONE, null);
	public static final Real MINUS_ONE =	from(BigDecimal.ONE.negate(), null);
	
	// TODO: complete the infinity semantics
	public static final Real POSITIVE_INFINITY = new Real();
	public static final Real NEGATIVE_INFINITY = new Real();
	
	

	/**
	 * Dedicated constructor for the infinities.
	 */
	private Real() {
		super(null, null);
	}
	
	private Real(final BigDecimal real, final String addr) {
		super(real, addr);
	}

	public static Real from(BigDecimal real, final String address) {
		if (real == null) throwInvalidityException("Null big decimals are NOT allowed!");
		
		Real ci = REAL_CACHE.get(real);	// cached Int
		if (ci == null) REAL_CACHE.put(real, ci = new Real(real, address));
		return ci;
	}
	
	public static Real from(final BigInteger intValue, final String address) {
		if (intValue == null) throwInvalidityException("Null big integers are NOT allowed!");
		return 
				from(new BigDecimal(intValue), address);
	}
	
	public static Real from(final String realValue, final String address) {
		if (realValue == null || realValue.isEmpty()) throwInvalidityException("Empty numbers are NOT allowed!");
		return 
				from(new BigDecimal(realValue), address);
	}
	
	public static Real from(final char[] realValue, final String address) {
		if (realValue == null || realValue.length == 0) throwInvalidityException("Empty numbers are NOT allowed!");
		return 
				from(new BigDecimal(realValue), address);
	}
	

	
	/* (non-Javadoc)
	 * @see ompca.conditionssion#getType()
	 */
	@Override
	public PlatformType getType() {
		return DataType.Real;
	}

	@Override
	final public Number<?> getZero() {
		return ZERO;
	}

	@Override
	final public Number<BigDecimal> getPositiveInfinity() {
		return POSITIVE_INFINITY;
	}
	
	@Override
	final public Number<BigDecimal> getNegativeInfinity() {
		return NEGATIVE_INFINITY;
	}

	
	
	@Override
	protected boolean equalsToCache(SystemElement e2) {
//		if (e2 instanceof Int) return equals(((Int) e2).toReal());
		if (e2 instanceof Int) try {
			return toIntExact().equals((Int) e2);
		} catch (NullPointerException e) {
		}
		return super.equalsToCache(e2);
	}
	
	
	
	@Override
	protected Boolean isLessThan(Number<?> n2) {
		assert n2 != null;
		if (n2 instanceof Int) return isLessThan(((Int) n2).toReal());
		return super.isLessThan(n2);
	}

	@Override
	public Boolean isZero() {
		return equals(ZERO);
	}

	@Override
	public Boolean isPositiveInfinity() {
		return this == POSITIVE_INFINITY;
	}
	
	@Override
	public Boolean isNegativeInfinity() {
		return this == NEGATIVE_INFINITY;
	}


	
	@Override
	public Expression negate() {
		if (isInfinity()) return this == POSITIVE_INFINITY
				? NEGATIVE_INFINITY : POSITIVE_INFINITY;
		return from(getValue().negate(), getShortAddress());
	}

	@Override
	protected ArithmeticExpression add(Number<?> n2) {
		assert n2 != null && !n2.isInfinity() && !isInfinity();
		if (n2 instanceof Real) return from(getValue().add(((Real) n2).getValue()), getShortAddress());
		if (n2 instanceof Int) return add(((Int) n2).toReal());
		throwTodoException("Unsupported number: " + n2 + "?");
		return null;
	}
	
	@Override
	protected ArithmeticExpression subtract(Number<?> n2) {
		assert n2 != null && !n2.isInfinity() && !isInfinity();
		if (n2 instanceof Real) return from(getValue().subtract(((Real) n2).getValue()), getShortAddress());
		if (n2 instanceof Int) return subtract(((Int) n2).toReal());
		throwTodoException("Unsupported number: " + n2 + "?");
		return null;
	}
	
	@Override
	protected ArithmeticExpression multiply(Number<?> n2) {
		assert n2 != null && !n2.isInfinity() && !isInfinity();
		if (n2 instanceof Real) return from(getValue().multiply(((Real) n2).getValue()), getShortAddress());
		if (n2 instanceof Int) return multiply(((Int) n2).toReal());
		throwTodoException("Unsupported number: " + n2 + "?");
		return null;
	}
	
	@Override
	protected ArithmeticExpression divide(Number<?> n2) {
		assert n2 != null && !n2.isInfinity() && !isInfinity();
		if (n2 instanceof Real) return from(getValue().divide(((Real) n2).getValue()), getShortAddress());
		if (n2 instanceof Int) return divide(((Int) n2).toReal());
		throwTodoException("Unsupported number: " + n2 + "?");
		return null;
	}
	
	
	
	public Int toInt() {
		if (isPositiveInfinity()) return Int.POSITIVE_INFINITY;
		if (isNegativeInfinity()) return Int.NEGATIVE_INFINITY;
		return Int.from(getValue().toBigInteger(), getShortAddress());
	}
	
	/**
	 * @return null for infinities since they're non-matchable
	 */
	public Int toIntExact() {
		try {
			return isInfinity() ? null : Int.from(getValue().toBigIntegerExact(), getShortAddress());
		} catch (ArithmeticException e) {
			return null;
		}
	}
	

	
	/**
	 * @see ompca.ompca.conditionement#toZ3SmtString(boolean, boolean, boolean)
	 */
	@Override
	public String toZ3SmtString(
		boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs) {
		if (isPositiveInfinity()) return VODCondGen.getPlatformPositiveInfinityReal();
		if (isNegativeInfinity()) return VODCondGen.getPlatformNegativeInfinityReal();
		return getValue().toPlainString();
	}
	
}