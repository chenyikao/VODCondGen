/**
 * 
 */
package ompca.vodcg;

import org.eclipse.cdt.core.dom.ast.ASTSignatureUtil;

import org.eclipse.cdt.core.CCorePlugin;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IBinding;
import org.eclipse.cdt.core.index.IIndex;
import org.eclipse.cdt.core.index.IndexFilter;
import org.eclipse.cdt.core.model.CoreModel;
import org.eclipse.cdt.core.model.CoreModelUtil;
import org.eclipse.cdt.core.model.ICProject;
import org.eclipse.cdt.core.model.ITranslationUnit;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.text.ITextSelection;

/**
 * Path to locate a variable in plain source code (not indexed model).
 *  
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class VariablePath {

	private static final IllegalArgumentException ILLEGAL_VP_EXCEPTION = 
			new IllegalArgumentException("Must provide a variable and its path!");
	
	private Assignable<?> lv;
	private int line;
	private IPath filePath;
	
	
	
//	private VariablePath(String varName, int varLine, IPath filePath, VOPCondGen condGen) 
//			throws CModelException, CoreException, InterruptedException {
//		if (varName == null || filePath == null) throw ILLEGAL_VP_EXCEPTION;
//		else set(varName, varLine, filePath, condGen);
//	}
	
	private VariablePath(Assignable<?> varLv, int varLine, IPath filePath) {
		set(varLv, varLine, filePath);
	}
	
	/**
	 * @param tvPath - the path to target variable in syntax <var:line@project/folder/file.c>
	 * @param condGen 
	 * @throws NumberFormatException 
	 */
	public VariablePath(String tvPath, VODCondGen condGen) throws NumberFormatException {
		final String[] tvpStruct = tvPath.split("[:@]");
		if (tvpStruct.length == 3) 
			set(tvpStruct[0], Integer.parseInt(tvpStruct[1]), new Path(tvpStruct[2]), condGen);
		else throw ILLEGAL_VP_EXCEPTION;
	}

	public static VariablePath from(
			ITextSelection selection, IPath filePath, VODCondGen condGen) {
		// Loading C-Index AST
//		final IIndex index = CCorePlugin.getIndexManager().getIndex(projs);	// findReferences(...) doesn't work!
//		while (true) {
//		try {
//			index.acquireReadLock(); // we need a read-lock on the index
//		} catch (InterruptedException e) {
//			continue;
//		} finally {
//			index.releaseReadLock();
//		}
//		}
			
		final IASTName varName = ASTUtil.getNameFrom(
				filePath, selection.getOffset(), selection.getLength(), true);
		if (varName != null) return new VariablePath(
				Assignable.from(varName, null, condGen), 
				varName.getFileLocation().getStartingLineNumber(), filePath);
		else return null;
			
	}
	


	public Assignable<?> getLValue() {
		return lv;
	}
	
	public IASTName getName() {
		return lv.getASTName();
	}
	
	public int getLine() {
		return line;
	}
	
	public IPath getFilePath() {
		return filePath;
	}



	private void set(Assignable<?> varLv, int varLine, IPath filePath) {
		if (varLv == null || varLine < 0 || filePath == null) 
			throw new IllegalArgumentException("Invalid variable path!");
//		if (var_name.getBinding() == null) set(var_name.getLastName().toString(), var_line, file_path);
//		else {
			lv = varLv;
			line = varLine;
			this.filePath = filePath;
//		}
	}
	
	private void set(String varName, int varLine, IPath filePath, VODCondGen condGen) {
		line = varLine;
		this.filePath = filePath;

		// Loading C-Index AST
		IIndex index = null;
//		while (true) {
			try {
				final ICProject[] projs = CoreModel.getDefault().getCModel().getCProjects();
				index = CCorePlugin.getIndexManager().getIndex(projs);
				index.acquireReadLock(); // we need a read-lock on the index
				final IASTTranslationUnit tvAST = CoreModelUtil.findTranslationUnitForLocation(
						filePath, projs[0]).getAST(index, ITranslationUnit.AST_SKIP_INDEXED_HEADERS);

				// org.eclipse.cdt.core.dom.ast.ASTNameCollector may be less efficient then the index tree
				final IBinding[] binds = index.findBindings(
						varName.toCharArray(), false, IndexFilter.ALL, new NullProgressMonitor());
				if (binds.length > 0) {
					final IASTName[] refs = tvAST.getReferences(binds[0]);
					if (refs.length > 0) lv = Assignable.from(refs[0], null, condGen);
				}
//				break;
//			
			} catch (InterruptedException | CoreException e) {
				e.printStackTrace();
//				continue;
			} finally {
				index.releaseReadLock();
			}
//		}
	}

	
	
	public String toString() {
		return ASTSignatureUtil.getExpressionString(lv.toASTExpression()) 
				+ ":" + line + "@" + filePath.toPortableString();
	}
}
