/**
 * 
 */
package ompca.vodcg;

import java.lang.reflect.Method;
import java.util.function.Supplier;

import ompca.DebugElement;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class UncertainException extends RuntimeException {

	/**
	 * 
	 */
	private static final long serialVersionUID = 3974036285728104447L;
	
	private SystemElement caller = null;
	private Method[] callees = null;
	
	private boolean excludesAssigners = false;
	private boolean excludesAssigneds = false;

	private Supplier<String> msg = null;
	
	
	
	public UncertainException(Exception source, 
			SystemElement caller, Method... callees) {
		this(source == null ? "" : source.toString(), source, caller, callees);
	}
	
	public UncertainException(String message, Exception source, 
			SystemElement caller, Method... callees) {
		super(source);
		this.caller = caller;
		this.callees = callees;
		msg = ()-> "Caused by " + message + "\n@ " 
				+ (caller == null ? "?" : caller) + " calling " 
				+ (callees == null || callees.length == 0 ? "?" : callees[0])
				+ (callees.length > 1 ? "..." : "");
	}

	
	
	public SystemElement getCaller() {return caller;}
	public Method[] getCallees() {return callees;}
	
	public UncertainException excludeAssigners() {
		excludesAssigners = true;
		return this;
	}
	public UncertainException excludeAssigneds() {
		excludesAssigneds = true;
		return this;
	}
	public boolean excludesAssigners() {return excludesAssigners;}
	public boolean excludesAssigneds() {return excludesAssigneds;}
	
	public <T> T leave() {
		if (caller == null || callees == null) 
			DebugElement.throwTodoException("nothing to leave", this);
		
		caller.leave(callees);
		caller = null;
		callees = null;
		return null;
	}

	public <T> T leave(final T result) {
		leave();
		return result;
	}
	
	@Override
	public String toString() {
		String str = msg == null ? "" : msg.get();
		if (caller != null || callees != null) str = "[Not leaved!] " + str;
		return str;
	}
	
}