/**
 * 
 */
package ompca.vodcg;

import java.util.SortedSet;

import org.eclipse.cdt.core.dom.ast.ASTGenericVisitor;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTName;

/**
 * @author Kao, Chen-yi
 *
 */
public class VODWritingHistoryObserver extends ASTGenericVisitor {

	/**
	 * @param wrs_ov - initial cache of writing references of OV
	 */
	public VODWritingHistoryObserver(SortedSet<IASTName> wrs_ov) {
		super(false);
		// TODO Auto-generated constructor stub
	}

	
	
	/**
	 * @param ov - observed variable, OV
	 * @param f - beginning function of observation
	 * @param observeSubcall - observing sub-function calls recursively or not
	 * @return
	 */
	public Iterable<IASTName> observe(IASTName ov, IASTFunctionDefinition f, boolean observeSubcall) {
		f.accept(this);
		// TODO Auto-generated method stub
		return null;
	}



	public Iterable<IASTName> observe(IASTName ov, IASTFunctionDefinition f) {
		// TODO: if ov is a pointer, return observe(ov, f, true);
		return observe(ov, f, false);
	}

}
