/**
 * 
 */
package ompca.vodcg.condition.data;

import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

import ompca.Addressable;
import ompca.Elemental;
import ompca.vodcg.ASTException;
import ompca.vodcg.ReenterException;
import ompca.vodcg.SystemElement;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.Expression;
import ompca.vodcg.condition.Function;
import ompca.vodcg.condition.VariablePlaceholder;

/**
 * The atomic constant arithmetic.
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
abstract public class Number<Value extends java.lang.Number & Comparable<Value>> 
extends Expression implements ArithmeticExpression, Addressable {
	
	private static final Method METHOD_IS_LESS_THAN = 
			Elemental.getMethod(Number.class, "isLessThan", NumericExpression.class);
	private static final Method METHOD_SUBTRACT = 
			Elemental.getMethod(Number.class, "subtract", ArithmeticExpression.class);
	
	
	
	private Value value;
	private java.lang.String address;
	
	/**
	 * A number is always globally constant.
	 * 
	 * @param value - null means (positive/negative) infinity.
	 */
	protected Number(final Value value, final java.lang.String address) {
		super(null, null);
		
//		if (value == null) 
//			throw new NullPointerException("Must provide some number!");
		this.value = value;
		this.address = address;
	}

	
	
	public Value getValue() {return value;}
	
	@Override
	public java.lang.String getShortAddress() {return address;}

//	@Override
//	public ThreadRole getThreadRole() {
//		return ThreadRole.CONST;
//	}
	
	
	
	/**
	 * Null value means (positive/negative) infinity.
	 * @return
	 */
	public final boolean isInfinity() {
		return value == null;
	}
	
	
	
	@Override
	protected Set<ArithmeticGuard> cacheArithmeticGuards() {
		return null;
	}
	
	/**
	 * A {@link Number} means a {@link Expression}-independent constant.
	 * 
	 * @return true always since its value is totally defined.
	 * @see ompca.condition.Expression#isConstant()
	 */
	@Override
	protected Boolean cacheConstant() {
		return true;
	}
	
	@Override
	protected Set<Function> cacheDirectFunctionReferences() {
		return null;
	}
	
	@Override
	protected <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType) {
		return null;
	}

	@Override
	protected void cacheDirectSideEffect() {
	}

	@Override
	protected Boolean cacheGlobal() {
		return true;
	}
	
	@Override
	public boolean containsArithmetic() {
		return true;
	}


	
	@Override
	public Boolean isZero() {
		if (isInfinity()) return false;
		return value.intValue() == 0;
	}

	@SuppressWarnings("unchecked")
	@Override
	public Boolean isPositive() {
		return isPositiveInfinity() || value.compareTo((Value) getZero().value) > 0;
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public Boolean isNegative() {
		return isNegativeInfinity() || value.compareTo((Value) getZero().value) < 0;
	}
	
	/* (non-Javadoc)
	 * @see ompca.condition.ArithmeticExpression#isLessThan(ompca.condition.ArithmeticExpression)
	 */
	@SuppressWarnings("unchecked")
	@Override
	public Boolean isLessThan(NumericExpression ae2) {
		if (ae2 == null) return null;
		
		// null value means (positive/negative) infinity
		Boolean result = null;
		if (isInfinity()) {		// separately null checking for infinity or not 
			if (isPositiveInfinity()) return false;									// oo < nothing
			else result = trySkipNullException(METHOD_IS_LESS_THAN,
					()-> !ae2.isNegativeInfinity());	// -oo < anything but -oo
		} else 					// ae2 maybe not infinity!
			result = trySkipNullException(METHOD_IS_LESS_THAN,
					()-> ae2.isPositiveInfinity() ? true : null,	// anything but oo < oo
					()-> ae2.isNegativeInfinity() ? false : null);	// nothing < -oo
		if (result != null) return result;
		
		if (ae2 instanceof Number<?>) return isLessThan((Number<?>) ae2);
		if (ae2 instanceof VariablePlaceholder) return isLessThan((VariablePlaceholder<?>) ae2);
//		VOPCondGen.throwTodoException("Unsupported number/variable!");
		return ArithmeticExpression.super.isLessThan(ae2);
	}
	
	@SuppressWarnings("unchecked")
	protected Boolean isLessThan(Number<?> n2) {
		assert n2 != null && value != null;
		return value.compareTo((Value) n2.value) < 0;
	}
	
	protected Boolean isLessThan(VariablePlaceholder<?> vd2) {
		if (vd2 == null) throwNullArgumentException("delegate");
		try {
			if (tests(vd2.isConstant())) return isLessThan(
					(ArithmeticExpression) vd2.getAssigner());
			
		} catch (ClassCastException e) {
			throwTodoException(e);
		} catch (ASTException e) {}
		return null;
	}
	


	@Override
	public Boolean equals(NumericExpression ne2) 
			throws ReenterException {
		if (ne2 instanceof Number<?>) return equalsToCache((Number<?>) ne2);
		return ArithmeticExpression.super.equals(ne2);
	}
	
	@Override
	protected boolean equalsToCache(SystemElement e2) 
			throws ClassCastException, NullPointerException {
		@SuppressWarnings("unchecked")
		final Number<Value> n2 = (Number<Value>) e2;
		if (isInfinity()) try {
			return n2.isInfinity() ? 
					ArithmeticExpression.super.equals(n2) : false;
		} catch (Exception e) {
			throwTodoException(e);
		}
		return value.equals(n2.value);
	}
	
	@Override
	protected List<Integer> hashCodeVars() {
		Integer hcv = null;
		if (isPositiveInfinity()) hcv = Integer.MAX_VALUE;
		else if (isNegativeInfinity()) hcv = Integer.MIN_VALUE;
		else {
			if (value == null) throwTodoException("unsupported infinity");
			hcv = value.intValue();
		}
		return Arrays.asList(hcv);
	}
	
	@Override
	public boolean suitsSideEffect() {
		return false;
	}
	
	
	
	@Override
	public ArithmeticExpression add(ArithmeticExpression ae2) {
		if (ae2 instanceof Number<?>) {
			final Number<?> n2 = (Number<?>) ae2;
			if (!isInfinity() && !n2.isInfinity()) return add(n2);
		}
		return ArithmeticExpression.super.add(ae2);
	}
	
	abstract protected ArithmeticExpression add(Number<?> n2);

	@Override
	public ArithmeticExpression subtract(ArithmeticExpression ae2) 
	throws ReenterException {
		try {
			return guardThrow(()-> {
				if (ae2 instanceof Number<?>) {
					final Number<?> n2 = (Number<?>) ae2;
					if (!isInfinity() && !n2.isInfinity()) return subtract(n2);
				}
				return ArithmeticExpression.super.subtract(ae2);},
					METHOD_SUBTRACT);
//			return debugCallDepth(50, (SystemElement) null, (TrySupplier<ArithmeticExpression>) ()-> 
//			super.subtract(ae2));

		} catch (ReenterException e) {
			throw e;
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	
	abstract protected ArithmeticExpression subtract(Number<?> n2);

	@Override
	public ArithmeticExpression multiply(ArithmeticExpression ae2) {
		if (ae2 instanceof Number<?>) {
			final Number<?> n2 = (Number<?>) ae2;
			if (!isInfinity() && !n2.isInfinity()) return multiply(n2);
		}
		return ArithmeticExpression.super.multiply(ae2);
	}
	
	abstract protected ArithmeticExpression multiply(Number<?> n2);

	@Override
	public ArithmeticExpression divide(ArithmeticExpression ae2) {
		if (ae2 instanceof Number<?>) {
			final Number<?> n2 = (Number<?>) ae2;
			if (Elemental.tests(n2.isZero())) throwInvalidityException("division by zero");
			if (!isInfinity() && !n2.isInfinity()) return divide(n2);
		}
		return ArithmeticExpression.super.divide(ae2);
	}
	
	abstract protected ArithmeticExpression divide(Number<?> n2);
	
	
	
	@SuppressWarnings("unchecked")
	@Override
	protected Number<Value> toConstantIf() {
		return this;
	}
	
	@Override
	protected java.lang.String toNonEmptyString(boolean usesParenthesesAlready) {
		return isInfinity() ? super.toNonEmptyString(usesParenthesesAlready) : value.toString();
	}

//	/* (non-Javadoc)
//	 * @see ompca.condition.ConditionElement#toZ3SmtString()
//	 */
//	@Override
//	public java.lang.String toZ3SmtString(
//			boolean printsVariableDeclaration, boolean printsFunctionDefinition) {
//		return toNonEmptyString(true);
//	}

}