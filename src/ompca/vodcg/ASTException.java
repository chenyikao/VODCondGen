/**
 * 
 */
package ompca.vodcg;

import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IBinding;
import org.eclipse.cdt.core.dom.ast.IProblemBinding;

/**
 * @author Kao, Chen-yi
 *
 */
public class ASTException extends IllegalArgumentException {

	private static final long serialVersionUID = 1L;
	
	public ASTException(IASTNode node) {
		super("unsupported AST node " + ASTUtil.toStringOf(node));
	}
	
	public ASTException(IBinding bind, Throwable cause) {
		super("non-AST binding? " + bind, cause);
	}
	
	public ASTException(IProblemBinding bind, Throwable cause) {
		super("AST binding problem? " + bind + 
				" " + ASTUtil.toStringOf(bind.getASTNode()), cause);
	}

}