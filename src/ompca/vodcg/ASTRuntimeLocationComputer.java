/**
 * 
 */
package ompca.vodcg;

import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTMacroExpansionLocation;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTNodeLocation;
import org.eclipse.cdt.core.dom.ast.IASTNodeSelector;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorPragmaStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.index.IIndexName;
import org.eclipse.core.runtime.CoreException;

import ompca.DebugElement;
import ompca.Elemental;
import ompca.TrioKeyMap;

/**
 * Comparing runtime locations between any AST nodes.
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class ASTRuntimeLocationComputer implements Comparator<IASTNode> {
	
//	private static final RuntimeLocationComparator Default = new RuntimeLocationComparator();
//	final private static Map<IFunction, IASTName> 	FIRST_CALLEE_CACHE = new HashMap<>();
	private static final Map<IASTName, IIndexName> 		INDEX_NAME_MAP = new HashMap<>();

	private static final TrioKeyMap<IASTNode, Class<? extends IASTNode>[], Class<? extends IASTNode>[], IASTNode> 
	PREVIOUS_CACHE = new TrioKeyMap<>();
	
	
	
//	private IIndex projectIndex;
	private VODCondGen condGen;



	public ASTRuntimeLocationComputer(VODCondGen condGen) {
		if (condGen == null) DebugElement.throwNullArgumentException("VOD condition generator");
//		this.projectIndex = projIndex;
		this.condGen = condGen;
	}
	
	
	
	/**
	 * For the target function F's callee reference F_ref:
	 * 	Main function has no callee reference.
	 * 	If the caller of F_ref, FCaller, is main, then the first (or direct) F_ref is the first callee of F.
	 * 	Else the first callee of F is the first callee of FCaller, which is FCaller_ref.
	 * 
	 * @param path - hosting both name (IASTName) and binding reference (IFunction) of F
	 * @return
	 */
//	public IASTName getFirstCalleeOfInMain(VOPWritingPath path) {
//		IFunction f = path.getHeadWritingFunc();	// the target function F for getting its first callee reference
//		
//		IASTName firstFRef = FIRST_CALLEE_CACHE.get(f);
//		if (firstFRef != null) return firstFRef;
//		
//		IASTName fname = path.getHeadWritingRefName();
//		if (condGen.isMainFunction(f)) firstFRef = fname;	// direct F_ref in main as the only callee of F
//		else {
//			
//			IBinding fCallerBind = f.getOwner();
//			// FCaller is a non-main enclosing function
//			if (fCallerBind != null) firstFRef = getFirstCalleeOfInMain(new VOPWritingPath(
//					ASTUtil.getAncestorOfAs(fname, IASTFunctionDefinition.class).getDeclarator().getName(), path));
//			else {
//				
//				int minPos = Integer.MAX_VALUE, fRefPos;
//				for (IBinding fRefBindOut : projectIndex.findBindings(
//						f.getNameCharArray(), false, IndexFilter.ALL, new NullProgressMonitor()))
//					// FCaller is defined (or F is called) in the other translation units
//					if (fRefBindOut != fname.resolveBinding()) {
//						
//						fCallerBind = fRefBindOut.getOwner();
//						// F ref is not a declaration and has an enclosing caller
//						if (fCallerBind != null && fCallerBind instanceof IFunction) {
//							IFunction fCaller = (IFunction) fCallerBind;
//							for (IName fRefOut : projectIndex.findReferences(fRefBindOut)) {
//								
//								if (condGen.isMainFunction(fCaller)) {
//									// 	If the caller of F_ref, FCaller, is main, then the first F_ref is the first callee of F.
//									fRefPos = fRefOut.getFileLocation().getNodeOffset();
//									if (fRefPos < minPos) {
//										minPos = fRefPos;
//										firstFRef = fRefOut;
//									}
//									
//								} else {
//									// 	Else the first callee of F is the first callee of FCaller, which is FCaller_ref.
//									IName fCallerRef = getFirstCalleeOfInMain(new VOPWritingPath(fRefOut, fCaller, path));
//									fRefPos = fCallerRef.getFileLocation().getNodeOffset();
//									if (fRefPos < minPos) {
//										minPos = fRefPos;
//										firstFRef = fCallerRef;
//									}
//								}
//							}
//						}
//					}
//			}
//		}
//		
//		return FIRST_CALLEE_CACHE.put(f, firstFRef);
//	}
	
	/**
	 * @param f - the target function F for getting its first callee reference
	 * @return
	 * @throws CoreException 
	 */
//	public IIndexName getFirstCalleeOf(IIndexName f) throws CoreException {
//		IIndexName firstFRef = FIRST_CALLEE_CACHE.get(f);
//		if (firstFRef != null) return firstFRef;
//		
//		// Main function has only it's definition entry as the callee reference
//		if (ASTUtil.isMainFunction(f)) firstFRef = f;
//		
//		int minPos = Integer.MAX_VALUE, fRefPos;
//		for (IIndexName fRef : projectIndex.findReferences(projectIndex.findBinding(f))) {
//			IIndexName fCaller = fRef.getEnclosingDefinition();
//			
//			if (ASTUtil.isMainFunction(fCaller)) {
//				// 	If the caller of F_ref, FCaller, is main, then the first F_ref is the first callee of F.
//				fRefPos = fRef.getFileLocation().getNodeOffset();
//				if (fRefPos < minPos) {
//					minPos = fRefPos;
//					firstFRef = fRef;
//				}
//				
//			} else {
//				// 	Else the first callee of F is the first callee of FCaller, which is FCaller_ref.
//				IIndexName fCallerRef = getFirstCalleeOf(fCaller);
//				fRefPos = fCallerRef.getFileLocation().getNodeOffset();
//				if (fRefPos < minPos) {
//					minPos = fRefPos;
//					firstFRef = fCallerRef;
//				}
//			}
//		}
//		
//		return FIRST_CALLEE_CACHE.put(f, firstFRef);
//	}

//	public IIndexName getFirstCalleeOf(IASTFunctionDefinition f) throws CoreException {
//		return getFirstCalleeOf(
//				projectIndex.findDefinitions(projectIndex.findBinding(ASTUtil.getNameOf(f)))[0]);
//	}
	


	public static void bind(IASTName aname, IIndexName iname) {
		INDEX_NAME_MAP.put(aname, iname);
	}



	/**
	 * @see java.util.Comparator#compare(java.lang.Object, java.lang.Object)
	 */
	@Override
	public int compare(IASTNode subject, IASTNode target) {
		try {
			return compare(
					ASTUtil.getAncestorsOfUntil(subject, ASTUtil.AST_FUNCTION_DEFINITION), 
					ASTUtil.getAncestorsOfUntil(target, ASTUtil.AST_FUNCTION_DEFINITION));
			
		} catch (CoreException | InterruptedException e) {
			return DebugElement.throwUnhandledException(e);
		}
	}

	public int compare(IASTFileLocation loc1, IASTFileLocation loc2) {
		if (loc1 == null || loc2 == null) throwIncomparableException("null file location");
		
		final String name1 = loc1.getFileName(), name2 = loc2.getFileName();
		return name1.equals(name2)
				? loc1.getNodeOffset() - loc2.getNodeOffset() 
				: name1.hashCode() - name2.hashCode();
	}
	


	/**
	 * @param ancestors1 - a traversal path of ancestors rooted by the enclosing function definition 
	 * 	of leaf node
	 * @param ancestors2 - a traversal path of ancestors rooted by the enclosing function definition 
	 * 	of leaf node
	 * @return
	 * @throws CoreException 
	 * @throws InterruptedException 
	 */
	private int compare(List<IASTNode> ancestors1, List<IASTNode> ancestors2) 
			throws CoreException, InterruptedException {
		if (ancestors1 == ancestors2) return 0;
		if (ancestors1 == null || ancestors2 == null) throwIncomparableException(); 
		
		IASTNode rootFunc1 = ancestors1.get(ancestors1.size()-1), 
				rootFunc2 = ancestors2.get(ancestors2.size()-1);
		// if the descendants are global...
		final Integer cag = compareAsGlobal(rootFunc1, rootFunc2);
		if (cag != null) return cag;
		
		// TODO: handling multiple references in a macro-expansion
		if (rootFunc1 == rootFunc2) {	// means they are in the same translation unit (global declaration)
			IASTNode leaf1 = ancestors1.get(0), leaf2 = ancestors2.get(0);
			if (leaf1 == null || leaf2 == null) throwIncomparableException();
			return leaf1.getFileLocation().getNodeOffset() - 
					leaf2.getFileLocation().getNodeOffset(); 
			
		} else {
			return VariableOrientedDag.from(((IASTFunctionDefinition)rootFunc1).getDeclarator().getName(), null, condGen)
					.getCalleeCompletedLocation() - 
					VariableOrientedDag.from(((IASTFunctionDefinition)rootFunc2).getDeclarator().getName(), null, condGen)
					.getCalleeCompletedLocation();
		}
	}



	/**
	 * ONLY for node host checking and comparison.
	 * 
	 * @param host1 - not necessarily {@link IASTFunctionDefinition}, assumed a top-level host 
	 * 	(translation unit) if given null
	 * @param host2 - the same assumption to {@link host1}
	 * @return
	 */
	protected static Integer compareAsGlobal(IASTNode host1, IASTNode host2) {
		if (host1 == null) return host2 == null ? 0 : Integer.MIN_VALUE;
		if (host2 == null) return host1 == null ? 0 : Integer.MAX_VALUE;
		return null;
	}



	/**
	 * @param node1
	 * @param node2
	 * @return
	 */
	public static int compareLocally(final IASTNode node1, final IASTNode node2) 
			throws IllegalArgumentException {
		if (node1 == node2) return 0; 
		if (node1 == null || node2 == null) 
			throwIncomparableException("Incomparable null node(s)!");
		
		final IASTFileLocation fl1 = node1.getFileLocation(), fl2 = node2.getFileLocation();
		if (fl1 == null || fl2 == null) 
			throwIncomparableException("Incomparable null file location(s)!");
		else if (!fl1.getFileName().equals(fl2.getFileName())) 
			throwIncomparableException("Incomparable different files!");
		else {	// file1 == file2
			final IASTFunctionDefinition func1 = ASTUtil.getWritingFunctionDefinitionOf(node1),
					func2 = ASTUtil.getWritingFunctionDefinitionOf(node2);
			if (func1 != func2) {	// declaration != main_function
				if (func1 == null) return -1;	// including condGen.isMainFunction(func2)
				if (func2 == null) return 1;	// including condGen.isMainFunction(func1)
				if (!func1.equals(func2)) throwIncomparableException("Incomparable local functions!");
			}
		}
		
		assert node1 != node2;
		int no1 = fl1.getNodeOffset(), no2 = fl2.getNodeOffset();
		if (no1 == no2) {
			final IASTNodeLocation[] ls1 = node1.getNodeLocations(), ls2 = node2.getNodeLocations();
			assert ls1 != null && ls2 != null;
			for (IASTNodeLocation l1 : ls1)
				for (IASTNodeLocation l2 : ls2)
					if (l1 instanceof IASTMacroExpansionLocation && l2 instanceof IASTMacroExpansionLocation) 
						return compareLocally((IASTMacroExpansionLocation) l1, (IASTMacroExpansionLocation) l2);
			DebugElement.throwTodoException("unsupported ambiguous nodes");
		}
		return no1 - no2;
	}

	public static int compareLocally(final IASTMacroExpansionLocation location1, final IASTMacroExpansionLocation location2) {
		if (location1 == location2) return 0; 
		if (location1 == null || location2 == null) 
			throwIncomparableException("Incomparable null location(s)!");
		
		return location1.getExpansion() == location2.getExpansion()
				? location1.getNodeOffset() - location2.getNodeOffset()
				: throwIncomparableException("Locally incomparable macros");
	}
	
//	public static int compareLocally(final IASTNodeLocation[] locations1, final IASTNodeLocation[] locations2) {
//		if (locations1 == locations2) return 0; 
//		if (locations1 == null || locations2 == null) 
//			throw new NullPointerException("Incomparable null location(s)!");
//		
//		Integer result = null;
//		for (IASTNodeLocation l1 : locations1)
//			for (IASTNodeLocation l2 : locations2)
//				if (l1 instanceof IASTFileLocation && l2 instanceof IASTFileLocation) {
//					result = compareLocally((IASTFileLocation) l1, (IASTFileLocation) l2);
//					break;
//				}
//		if (result == 0) 
//			for (IASTNodeLocation l1 : locations1)
//				for (IASTNodeLocation l2 : locations2)
//					if (l1 instanceof IASTMacroExpansionLocation && l2 instanceof IASTMacroExpansionLocation) {
//						result = compareLocally((IASTMacroExpansionLocation) l1, (IASTMacroExpansionLocation) l2);
//						break;
//					}
//		return result; 
//	}
	
	
	
	/**
	 * Excluding the case that subject is the same as target.
	 * 
	 * @param subject
	 * @param target
	 * @return
	 */
	public boolean isBefore(IASTNode subject, IASTNode target) {
		return compare(subject, target) < 0;
	}

	/**
	 * @param node1
	 * @param node2
	 * @return true if {@code node1} exclusively before {@code node2} 
	 * 	in execution order, given both of them appear in the same file;
	 * 	Or false if they are not in the order;
	 *  Or null if they are incomparable.
	 */
	public Boolean isBeforeLocally(IASTNode node1, IASTNode node2) {
		try {
			return compareLocally(node1, node2) < 0;
		} catch (NullPointerException | IllegalArgumentException e) {
			return null;
		}
	}
	


	public boolean isIn(IASTNode subject, IASTNode target) {
		List<IASTNode> subjectFunc = 
				ASTUtil.getAncestorsOfUntil(subject, ASTUtil.AST_FUNCTION_DEFINITION);
		return (subjectFunc == null) ? false : subjectFunc.containsAll(
				ASTUtil.getAncestorsOfUntil(target, ASTUtil.AST_FUNCTION_DEFINITION)); 
	}

	public boolean isAfter(IASTNode subject, IASTNode target) {
		return compare(subject, target) > 0;
	}

	
	
	@SuppressWarnings("unchecked")
	public <SiblingAs extends IASTNode, SiblingIg extends IASTNode> 
	SiblingAs previousOfAsIgnoring(
			IASTNode me, Class<SiblingAs>[] asTypes, Class<SiblingIg>[] ignoredTypes) {
		if (me == null || asTypes == null || asTypes.length == 0) return null;
		
//		SMALLEST_BIG_SIBLING_CACHE.clear();
		SiblingAs result = (SiblingAs) PREVIOUS_CACHE.get(me, asTypes, ignoredTypes);
		if (result != null) return result;
		
//		final int[] start = {me.getFileLocation().getNodeOffset() - 1}, length = {1};
		final boolean includesPragma = ASTUtil.superclasses(asTypes, ASTUtil.AST_PRAGMA);
//		final IASTTranslationUnit tu = me.getTranslationUnit();
//		final IASTNodeSelector ns = tu.getNodeSelector(null);
//		IASTNode pre = previousOfContained(me, start, length, includesPragma, tu, ns);
		IASTNode pre = previousOf(me, includesPragma);
		traverseSibling: while (pre != null) {
			typeChecking: {
			for (Class<SiblingIg> igt : ignoredTypes)
				if (igt.isInstance(pre)) break typeChecking;
			for (Class<SiblingAs> ast : asTypes) 
				if (ast.isInstance(pre)) {result = (SiblingAs) pre; break traverseSibling;}
			}
			// !(pre instanceof SiblingAs)
			pre = previousOf(pre, includesPragma);
//			pre = previousOfContained(pre, start, length, includesPragma, tu, ns);
		}
		
		PREVIOUS_CACHE.put(me, asTypes, ignoredTypes, result);
		return result;
	}
	
	/**
	 * @param me
	 * @param includesPragma
	 * TODO: @param includesComment 
	 * @return the last descendant (direct biggest small sibling) node of {@code me} in AST.
	 * 	Or the parent node of {@code me} if {@code me} is already the smallest sibling.
	 */
	public IASTNode previousOf(final IASTNode me, final boolean includesPragma) {
		if (me == null) DebugElement.throwInvalidityException("me");

		IASTNode parent = ASTUtil.getParentOf(me);
		if (parent == null) return null;
		
		// regular child node s should be in AST order
		IASTNode pre = null;
		final boolean isPragma = me instanceof IASTPreprocessorPragmaStatement;
		for (IASTNode sbl : parent.getChildren()) {
			if (isPragma) {
				final Boolean isSblPre = isBeforeLocally(sbl, me);
				if (isSblPre == null) DebugElement.throwTodoException("unsupported pragma");
				else if (!isSblPre) break;
			} else 
				if (sbl == me) break;
			
			pre = sbl;
		}
		pre = pre == null 
				? parent							// when sbl is the first child
				: ASTUtil.getLastDescendantOf(pre);	// or going deeper
		
		if (includesPragma) {
			final IASTNode pp = previousPragmaOfAfter(me, pre, me.getTranslationUnit()); 
			pre = pp == null ? pre : pp;
		}

		/* TODO: comments are NOT included as regular child nodes. 
		 * Neither {@link IASTNodeSelector} finds comments.
		 */
		return pre;
	}
	
	/**
	 * Pragmas are NOT included as regular child nodes. 
	 * Neither {@link IASTNodeSelector} finds preprocessor statements.
	 * 
	 * @param me
	 * @param pre
	 * @param tu
	 * @param CondGen 
	 * @return
	 */
	public IASTPreprocessorPragmaStatement previousPragmaOfAfter(
			final IASTNode me, IASTNode pre, IASTTranslationUnit tu) {
		if (me == null) DebugElement.throwInvalidityException("me");
		
		if (tu == null) tu = me.getTranslationUnit();
		for (IASTPreprocessorPragmaStatement p : ASTUtil.getPragmas(tu)) 
			if (ASTUtil.isInTheSameFile(p, me)) 
				if (pre == null || 
				(Elemental.tests(isBeforeLocally(pre, p)) && Elemental.tests(isBeforeLocally(p, me))))
					pre = p;
		return pre instanceof IASTPreprocessorPragmaStatement ?
				(IASTPreprocessorPragmaStatement) pre : null;
	}
	
	
	
	static public <T> T throwIncomparableException() {
		return throwIncomparableException((String) null);
	}
	
	static public <T> T throwIncomparableException(final IllegalArgumentException e) {
		return throwIncomparableException(null, e);
	}
	
	static public <T> T throwIncomparableException(String message) {
		return throwIncomparableException(message, null);
	}
	
	static public <T> T throwIncomparableException(String message, Throwable e) {
		if (message == null) message = "incomparable ones";
		throw new IncomparableException(message, e);
	}
	
}