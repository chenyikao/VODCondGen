/**
 * 
 */
package ompca.vodcg;

import java.lang.reflect.Method;

/**
 * @author Kao, Chen-yi
 *
 */
public class UncertainPlaceholderException extends UncertainException {

	private static final long serialVersionUID = 2658480034812631970L;


	
	public UncertainPlaceholderException(String message, Exception cause, 
			Assignable<?> asn, Method... callees) {
		super(message, cause, asn, callees);
	}
	
	@Override
	public <T> T leave() {
		final Throwable cause = getCause();
		if (cause instanceof UncertainException)
			return ((UncertainException) cause).leave();
		
		return super.leave();
	}
	
}