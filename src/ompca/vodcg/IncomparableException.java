/**
 * 
 */
package ompca.vodcg;

/**
 * This class is extended from IllegalArgumentException for denoting both argument and non-argument incomparability.
 * 
 * @author Kao, chen-yi
 *
 */
public class IncomparableException extends IllegalArgumentException {

	/**
	 * 
	 */
	private static final long serialVersionUID = 8332030608603538968L;

	public IncomparableException(String message) {
		super(message);
	}
	
	public IncomparableException(String message, Throwable cause) {
		super(message, cause);
	}
	
	public IncomparableException(SystemElement se1, SystemElement se2, 
			String message, Exception cause) {
		super("Incomparable " + message + ": " 
			+ (se1 == null ? "(null)" : se1.toString()) + "\n\tand " 
				+ (se2 == null ? "(null)" : se2.toString()), cause);
	}
	
}