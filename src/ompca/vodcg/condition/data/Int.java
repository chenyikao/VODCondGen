/**
 * 
 */
package ompca.vodcg.condition.data;

import java.lang.String;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTForStatement;

import ompca.vodcg.ASTAddressable;
import ompca.vodcg.ASTLoopUtil;
import ompca.vodcg.SystemElement;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.Expression;

/**
 * @author Kao, Chen-yi
 *
 */
public class Int extends Number<BigInteger> {
	
	// must be initialized first! (as in the source code order)
	private static final Map<BigInteger, Int> INT_CACHE = new HashMap<>();
	
	

	public final static Int ZERO = 		from(BigInteger.ZERO, null);
	public final static Int ONE = 		from(BigInteger.ONE, null);
	public final static Int MINUS_ONE = from(BigInteger.ONE.negate(), null);
	
	// TODO: complete the infinity semantics
	public static final Int POSITIVE_INFINITY = new Int();
	public static final Int NEGATIVE_INFINITY = new Int();
	
	
	
	/**
	 * Dedicated constructor for the infinities.
	 */
	private Int() {
		super(null, null);
	}
	
	private Int(final BigInteger i, final String address) {
		super(i, address);
	}
	
//	private Int(int i) {
//		this(BigInteger.valueOf(i));
//	}

	public static Int from(BigInteger i, final String address) {
		if (i == null) throwInvalidityException("Null big integers are NOT allowed!");

		Int ci = INT_CACHE.get(i);	// cached Int
		if (ci == null) INT_CACHE.put(i, ci = new Int(i, address));
		return ci;
	}
	
	public static Int from(Integer intValue, final String address) {
		if (intValue == null) throwInvalidityException("Null integers are NOT allowed!");
		return 
				from(BigInteger.valueOf(intValue), address);
	}
	
	/**
	 * @param longValue
	 * @return
	 */
	public static Int from(Long longValue, final String address) {
		if (longValue == null) throwInvalidityException("Null long integers are NOT allowed!");
		return 
				from(BigInteger.valueOf(longValue), address);
	}

	public static Int from(String intValue, final String address) {
		if (intValue == null || intValue.isEmpty()) throwInvalidityException("Empty numbers are NOT allowed!");
		return 
				from(new BigInteger(intValue), address);
	}
	
	public static Int from(final char[] intValue, final String address) {
		if (intValue == null || intValue.length == 0) throwInvalidityException("Empty numbers are NOT allowed!");
		return 
				from(String.valueOf(intValue), address);
	}
	
	/**<pre>
	 * 		incr-expr 	One of the following:
	 * 					++var
	 * 					var++
	 * 					--var
	 * 					var--
	 * 					var += incr
	 * 					var -= incr
	 * 					var = var + incr
	 *					var = incr + var
	 * 					var = var - incr
	 * 
	 *		var 		One of the following:
	 *						A variable of a signed or unsigned integer type.
	 *						TODO: For C++, a variable of a random access iterator type.
	 *						TODO: For C, a variable of a pointer type.
	 *					If this variable would otherwise be shared, it is implicitly made private in the
	 *					loop construct. This variable must not be modified during the execution of the
	 *					for-loop other than in incr-expr. Unless the variable is specified lastprivate
	 *					or linear on the loop construct, its value after the loop is unspecified.
	 * 
	 *		incr 		A loop invariant integer expression.
	 * <br>
	 * 
	 * @param loop
	 * @param sideEffect 
	 * @param condGen 
	 * @return
	 */
	public static Int fromCanonicalIncrementOf(IASTForStatement loop, final ASTAddressable dynaAddr, VODCondGen condGen) {
		if (ASTLoopUtil.isNonCanonical(loop)) return null;
		
		Int incr = ASTLoopUtil.getIncrementOf(loop);
		if (incr == null) {
			ArithmeticExpression e = ArithmeticExpression.fromIncrementOf(loop, dynaAddr, condGen);
			incr = (e instanceof Int) ? (Int) e : null;	// type-checking
			
			if (incr == null) ASTLoopUtil.setNonCanonical(loop);
			else ASTLoopUtil.setIncrementOf(loop, incr);
		}
		return incr;
	}
	
	
	
	/* (non-Javadoc)
	 * @see ompca.condition.Expression#getType()
	 */
	@Override
	public PlatformType getType() {
		return DataType.Int;
	}

	@Override
	final public Number<?> getZero() {
		return ZERO;
	}

	@Override
	final public Number<BigInteger> getPositiveInfinity() {
		return POSITIVE_INFINITY;
	}
	
	@Override
	final public Number<BigInteger> getNegativeInfinity() {
		return NEGATIVE_INFINITY;
	}

	
	
	@Override
	protected boolean equalsToCache(SystemElement e2) 
			throws ClassCastException, NullPointerException {
		if (e2 instanceof Real) {
			if (isInfinity()) return false;
			return toReal().equals((Real) e2);
		}
		return super.equalsToCache(e2);
	}
	
	
	
	@Override
	protected Boolean isLessThan(Number<?> n2) {
		assert n2 != null;
		if (n2 instanceof Real) return toReal().isLessThan((Real) n2);
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
		if (n2 instanceof Int) return from(getValue().add(((Int) n2).getValue()), getShortAddress());
		if (n2 instanceof Real) return toReal().add((Real) n2);
		throwTodoException("Unsupported number: " + n2);
		return null;
	}
	
	@Override
	protected ArithmeticExpression subtract(Number<?> n2) {
		assert n2 != null && !n2.isInfinity() && !isInfinity();
		if (n2 instanceof Int) return from(getValue().subtract(((Int) n2).getValue()), getShortAddress());
		if (n2 instanceof Real) return toReal().subtract((Real) n2);
		throwTodoException("Unsupported number: " + n2);
		return null;
	}
	
	@Override
	protected ArithmeticExpression multiply(Number<?> n2) {
		assert n2 != null && !n2.isInfinity() && !isInfinity();
		if (n2 instanceof Int) return from(getValue().multiply(((Int) n2).getValue()), getShortAddress());
		if (n2 instanceof Real) return toReal().multiply((Real) n2);
		throwTodoException("Unsupported number: " + n2);
		return null;
	}
	
	@Override
	protected ArithmeticExpression divide(Number<?> n2) {
		assert n2 != null && !n2.isInfinity() && !isInfinity();
		if (n2 instanceof Int) return from(getValue().divide(((Int) n2).getValue()), getShortAddress());
		if (n2 instanceof Real) return toReal().divide((Real) n2);
		throwTodoException("Unsupported number: " + n2);
		return null;
	}
	
	
	
	/**
	 * @return null for integer infinities since they're non-matchable
	 */
	final public Real toReal() {
		return isInfinity() ? null : Real.from(getValue(), getShortAddress());
	}
	
	

	public String toNonEmptyString(boolean usesParenAlready) {
		return isInfinity() ? 
				super.toNonEmptyString(usesParenAlready) : String.valueOf(getValue());
	}

	/**
	 * @see ompca.condition.ConditionElement#toZ3SmtString(boolean, boolean, boolean)
	 */
	@Override
	public String toZ3SmtString(
		boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs) {
		if (isPositiveInfinity()) return VODCondGen.getSimulatedPositiveInfinityInt();
//		if (isPositiveInfinity()) return VODCondGen.getPlatformPositiveInfinityInt();
		if (isNegativeInfinity()) return VODCondGen.getPlatformNegativeInfinityInt();
		return getValue().toString();
	}
	

}