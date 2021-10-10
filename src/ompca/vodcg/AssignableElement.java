/**
 * 
 */
package ompca.vodcg;

import java.util.function.Supplier;

import ompca.Elemental;
import ompca.vodcg.condition.Expression;

/**
 * @author Kao, chen-yi
 *
 */
public interface AssignableElement {

	/**
	 * @return null if uncertain, like checking indirect argument assigned-ness during 
	 * AST parsing of function calls
	 */
	default public Boolean isAssigned() {
		return Elemental.tests(()-> getAssignable().isAssigned());
	}
	
	default public boolean isSelfAssigned() {
		return getAssigner() == this;
	}
	
//	default public boolean isInAST() {
//		return true;
//	}
	
	
	
	static public <T> T getAsn(Supplier<T> sup) {
		return getAsn(sup, ()-> null);
	}
	
	static public <T> T getAsn(Supplier<T> sup, Supplier<T> nullAlt) {
		try {
			return Elemental.getNonNullSupplier(sup);
			
		} catch (NullPointerException | ReenterException e) {	// may NOT be thrown directly from sup
			if (nullAlt == null) SystemElement.throwTodoException("non-assignable");
			return nullAlt.get();
			
		} catch (Exception e) {				// non-null exception with conditional halting
			return SystemElement.throwTodoException(e);
		}
	}
	
	public Assignable<?> getAssignable();
	
	/**
	 * @return null if not assigned.
	 */
	default public Expression getAssigner() {
		return Elemental.tests(isAssigned())
				? getAssignerIf()
				: null;
	}
	
	/**
	 * Should be invoked only if assigned.
	 * @return non-null
	 */
	default Expression getAssignerIf() {
		return getAsn(()-> getAssignable().getAssigner(),
				()-> throwUnsupportedException());
	}
	
//	public AssignableElement previousAssigned();

	default public <T> T throwUnsupportedException() {
		return SystemElement.throwTodoException(
				"unsupported assignable element");
	}
	
}