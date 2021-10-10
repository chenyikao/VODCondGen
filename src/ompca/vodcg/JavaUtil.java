/**
 * 
 */
package ompca.vodcg;

/**
 * @author Kao, Chen-yi
 *
 */
public final class JavaUtil {

	@SuppressWarnings("unchecked")
	public static final Class<Exception>[] NULL_POINTER_EXCEPTION_CLASS 
	= new Class[] {NullPointerException.class};
	
	@SuppressWarnings("unchecked")
	public static final Class<Exception>[] NULL_CLASS_CAST_EXCEPTION_CLASS 
	= new Class[] {NullPointerException.class, ClassCastException.class};
	
	@SuppressWarnings("unchecked")
	public static final Class<Exception>[] NULL_CLASS_CAST_UNCERTAIN_EXCEPTION_CLASS 
	= new Class[] {NullPointerException.class, ClassCastException.class, 
			UncertainException.class, UncertainPlaceholderException.class};
	
	@SuppressWarnings("unchecked")
	public static final Class<Exception>[] AST_NULL_CLASS_CAST_UPLACEHOLDER_EXCEPTION_CLASS 
	= new Class[] {ASTException.class, NullPointerException.class, 
			ClassCastException.class, UncertainPlaceholderException.class};
	
	@SuppressWarnings("unchecked")
	public static final Class<Exception>[] AST_NULL_CLASS_CAST_REENTER_EXCEPTION_CLASS 
	= new Class[] {ASTException.class, NullPointerException.class, 
			ClassCastException.class, ReenterException.class};
	
}