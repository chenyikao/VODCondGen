/**
 * 
 */
package ompca.vodcg.condition;

import java.util.NavigableSet;
import java.util.function.Supplier;

import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.Elemental;
import ompca.vodcg.ASTException;
import ompca.vodcg.Assignable;
import ompca.vodcg.AssignableElement;
import ompca.vodcg.Assignment;
import ompca.vodcg.IncomparableException;
import ompca.vodcg.ReenterException;
import ompca.vodcg.SystemElement;
import ompca.vodcg.condition.data.NumericExpression;
import ompca.vodcg.parallel.OmpDirective;
import ompca.vodcg.parallel.ThreadPrivatizable;

/**
 * Assignable arithmetic expression.
 * @author Kao, Chen-yi
 *
 */
public interface AssignableExpression 
extends ArithmeticExpression, AssignableElement, ThreadPrivatizable {

	default public void guard(Runnable runnable) {
		try {
			getAssignable().guard(runnable);
			
		} catch (NullPointerException e) {
			SystemElement.throwTodoException(e);
		}
	}
	
	default public <T> T guard(Supplier<T> returnSupplier) {
		return guard(returnSupplier, ()-> null);
	}
	
	default public <T> T guard(Supplier<T> returnSupplier, 
			Supplier<T> reenterSupplier) {
//		return AssignableExpression.this.guard(returnSupplier, reenterSupplier, null);
		try {
			return getAssignable().guard(
					returnSupplier, 
					reenterSupplier);
			
		} catch (NullPointerException e) {
			final SystemElement se = (SystemElement) this;
//			return se.debugGet(()-> se.guard(
			return se.guard(
					returnSupplier, 
					reenterSupplier);
			
		} catch (ClassCastException e) {
			return SystemElement.throwTodoException(e);
		}
	}
	
//	default public <T> T guard(Supplier<T> returnSupplier, 
//			Supplier<T> reenterSupplier, Method callee) {
//		try {
//			return getAssignable().guard(
//					returnSupplier, 
//					reenterSupplier,
//					callee);
//			
//		} catch (NullPointerException e) {
//			final SystemElement se = (SystemElement) this;
//			return se.debugGet(()-> se.guard(
//					returnSupplier, 
//					reenterSupplier,
//					callee));
//			
//		} catch (ClassCastException e) {
//			return SystemElement.throwTodoException(e);
//		}
//	}

	
	
	static public <T> T getAsnNonNull(Supplier<T> sup) {
		return AssignableElement.getAsn(sup, null);
	}
	
	
	
	/**
	 * @return null if not assigned.
	 */
	default public Assignment getAssignment() {
		return Elemental.tests(isAssigned())
				? getAssignmentIf()
				: null;
	}

	/**
	 * Should be invoked only if assigned.
	 * @return null only if this is non-AST.
	 */
	default Assignment getAssignmentIf() {
		return AssignableElement.getAsn(()-> 
		getAssignable().getFirstAssignment());
	}
	
	
	
	default public void setAssigner(Expression rhs) {
//		if (Elemental.testsNot(isAssigned())) SystemElement.throwTodoException("inconsistent assignedness");
		if (rhs == null) setAssigned((Boolean) null);
		else setAssigned();
	}
	
//	public void setAssignment(Assignment asm);
	
	default public void setAssigned() {setAssigned(true);}
	public void setAssigned(Boolean isAssigned);
	
	default public void setAssigned(Expression rhs) {
		setAssigner(rhs);	//asm.setAssigned(this, rhs);
//		setAssigner(rhs.cloneReversion(getPrivatizingBlock(), getAssigned().getThreadRole(), null));	//asm.setAssigned(this, rhs);
		assert rhs != null;
//		if (asm == null) return;	// may be called before asm ready
//		setAssignment(asm);	
//		if (rhs instanceof AssignableExpression) ((AssignableExpression) rhs).setAssignment(asm);
	}
	
	default public boolean hasAssignable() {
		return getAssignable() != null;
	}
	
	default public boolean isLikelyAssigned() {
		return Elemental.tests(isAssigned());
	}
		
	@Override
	default public Boolean isAssigned() {
		return AssignableElement.getAsn(()-> getAssignable().isAssigned(),
				()-> throwUnsupportedException());
	}
	
	/**
	 * @return true if this is an AST or non-AST argument.
	 */
	default public boolean isArgument() {
		return getAsnNonNull(()-> 
		getAssignable().isArgument());
	}
	
	@Override
	default public Boolean isConstant() {
		return getAsnNonNull(()-> 
		getAssignable().isConstant());
	}
	
	@Override
	default public boolean isFunctional() {
		return SystemElement.tests(getAsnNonNull(()-> 
		getAssignable().isFunctional()));
	}
	
	default public boolean isUnsigned() throws IncomparableException {
		return getAsnNonNull(()-> 
		getAssignable().isUnsigned());
	}
	
	/**
	 * @return true only possibly if it's type is numeric. 
	 */
	@Override
	default public Boolean isZero() 
			throws ASTException {
		if (getType().isNumeric()) {
			if (Elemental.tests(isAssigned())) {
				final Assignable<?> asn = getAssignable();
				if (asn != null && asn.selfAssigns()) {
					if (asn.isLoopIterator()) {
						final SystemElement lr = ExpressionRange.fromIteratorOf(
								asn.getEnclosingCanonicalLoop(), 
								asn.getRuntimeAddress(),
								asn.getCondGen()).toConstant();
						if (lr == null) return null;
						if (lr instanceof NumericExpression)
							return ((NumericExpression) lr).isZero();
						SystemElement.throwTodoException("unsupported loop iterator");
					}
					
					final Expression pAsnr = asn.previousAssigner();
					if (pAsnr == null) return null;	// non-initialized
					if (pAsnr instanceof NumericExpression)
						return ((NumericExpression) pAsnr).isZero();
					SystemElement.throwTodoException("unsupported assigner");
				}
				
				final Expression asnr = getAssigner();
				if (asnr == null) return null;	// non-initialized
				if (asnr instanceof NumericExpression)
					return ((NumericExpression) asnr).isZero();
				SystemElement.throwTodoException("unsupported assigner");
			}
		}
		return ArithmeticExpression.super.isZero();
	}
	
	/**
	 * Faster checking for constant variables.
	 * Non-assigned means unknown value and scale.
	 * 
	 * @see ompca.condition.ArithmeticExpression#isPositive()
	 */
	@SuppressWarnings("unchecked")
	@Override
	default public Boolean isPositive() throws ReenterException {
		return trySkipNullException(
				getMethod(AssignableExpression.class, "isPositive"),
				// main return
				()-> getAssignable().isUnsigned(),
				()-> ((NumericExpression) getAssigner()).isPositive(),
				()-> ArithmeticExpression.super.isPositive());
	}
	
	/**
	 * Faster checking for constant variables.
	 * Non-assigned means unknown value and scale.
	 * 
	 * @see ompca.condition.ArithmeticExpression#isPositiveInfinity()
	 */
	@SuppressWarnings("unchecked")
	@Override
	default public Boolean isPositiveInfinity() throws ReenterException {
		return trySkipNullException(
				getMethod(AssignableExpression.class, "isPositiveInfinity"),
				// main return
				()-> ((NumericExpression) getAssigner()).isPositiveInfinity(),
				()-> ArithmeticExpression.super.isPositiveInfinity());
	}
	
	@SuppressWarnings("unchecked")
	@Override
	default public boolean isPrivate() {
		try {
			return trySkipNullException(
					()-> isThreadPrivate(),
					()-> getAssignable().isThreadPrivate(),
					()-> ArithmeticExpression.super.isPrivate());
			
		} catch (Exception e) {
			return SystemElement.throwTodoException(e);
		}
	}

	
	
	/**
	 * Faster checking for constant variables.
	 * Non-assigned means unknown value and scale.
	 * 
	 * @see ompca.condition.ArithmeticExpression#isNegative()
	 */
	@SuppressWarnings("unchecked")
	@Override
	default public Boolean isNegative() throws ReenterException {
		return trySkipNullException(
				getMethod(AssignableExpression.class, "isNegative"),
				// main return
				()-> isSelfAssigned() ? ((NumericExpression) getAssigner()).isNegative() : null,
				()-> ArithmeticExpression.super.isNegative());
	}
	
	/**
	 * Faster checking for constant variables.
	 * Non-assigned means unknown value and scale.
	 * 
	 * @see ompca.condition.ArithmeticExpression#isNegativeInfinity()
	 */
	@SuppressWarnings("unchecked")
	@Override
	default public Boolean isNegativeInfinity() throws ReenterException {
		return trySkipNullException(
				getMethod(AssignableExpression.class, "isNegativeInfinity"),
				// main return
				()-> ((NumericExpression) getAssigner()).isNegativeInfinity(),
				()-> ArithmeticExpression.super.isNegativeInfinity());
	}
	
	
	
	@SuppressWarnings("unchecked")
	default public Boolean equals(AssignableExpression ae2) 
			throws ReenterException {
		if (ae2 == null) return SystemElement.throwNullArgumentException("assignable expression");
		return trySkipNullException(
				getMethod(AssignableExpression.class, "equals", AssignableExpression.class),
				// main return - initializer list elements share the same assignment but are not necessarily equal
				()-> getAssignment() != ae2.getAssignment() ? false : null,
				()-> ArithmeticExpression.super.equals(ae2));
	}

	
	
	/**
	 * @return non-null if the assignable exists
	 */
	default public NavigableSet<OmpDirective> getEnclosingDirectives() {
		return AssignableElement.getAsn(()-> 
		getAssignable().getEnclosingDirectives());
	}
	
	@Override
	default public IASTStatement getPrivatizingBlock() {
		return AssignableElement.getAsn(()-> 
		getAssignable().getPrivatizingBlock());
	}
	
	default public <T> T throwUnsupportedException() {
		return SystemElement.throwTodoException(
				"unsupported assignable expression");
	}
	
}