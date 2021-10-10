/**
 * 
 */
package ompca.vodcg;

import java.lang.reflect.Method;
import java.util.function.Supplier;

/**
 * @author Kao, Chen-yi
 *
 */
public class ReenterException extends UncertainException {

	private static final long serialVersionUID = 5685409621301029871L;


	
	public ReenterException(SystemElement caller, Method... callees) {
		super("re-entering", null, caller, callees);
		if (caller == null) 
			SystemElement.throwNullArgumentException("caller");
		if (callees == null || callees.length == 0) 
			SystemElement.throwNullArgumentException("callee");
	}
	
	public ReenterException(SystemElement caller, Supplier<?> callee) {
		super("re-entering lambda", null, caller);
		if (caller == null) 
			SystemElement.throwNullArgumentException("caller");
		if (callee == null) 
			SystemElement.throwNullArgumentException("callee");
	}
	
}