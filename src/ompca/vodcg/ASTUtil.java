/**
 * 
 */
package ompca.vodcg;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.cdt.core.CCorePlugin;
import org.eclipse.cdt.core.dom.IName;
import org.eclipse.cdt.core.dom.ast.ASTGenericVisitor;
import org.eclipse.cdt.core.dom.ast.ASTNameCollector;
import org.eclipse.cdt.core.dom.ast.ASTSignatureUtil;
import org.eclipse.cdt.core.dom.ast.DOMException;
import org.eclipse.cdt.core.dom.ast.EScopeKind;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTCaseStatement;
import org.eclipse.cdt.core.dom.ast.IASTComment;
import org.eclipse.cdt.core.dom.ast.IASTDefaultStatement;
import org.eclipse.cdt.core.dom.ast.IASTDoStatement;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNameOwner;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTNodeLocation;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorPragmaStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;
import org.eclipse.cdt.core.dom.ast.IASTReturnStatement;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.core.dom.ast.IBinding;
import org.eclipse.cdt.core.dom.ast.IEnumeration;
import org.eclipse.cdt.core.dom.ast.IFunction;
import org.eclipse.cdt.core.dom.ast.IParameter;
import org.eclipse.cdt.core.dom.ast.IProblemBinding;
import org.eclipse.cdt.core.dom.ast.IType;
import org.eclipse.cdt.core.index.IIndex;
import org.eclipse.cdt.core.index.IIndexBinding;
import org.eclipse.cdt.core.index.IIndexManager;
import org.eclipse.cdt.core.index.IndexFilter;
import org.eclipse.cdt.core.model.CoreModel;
import org.eclipse.cdt.core.model.CoreModelUtil;
import org.eclipse.cdt.core.model.ICProject;
import org.eclipse.cdt.core.model.ITranslationUnit;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;

import ompca.DebugElement;
import ompca.DuoKeyMap;
import ompca.Elemental;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public final class ASTUtil extends DebugElement {

	static final int prime = 31;
	public static final int r_any = 
			prime * (prime * (prime * IASTNameOwner.r_declaration 
					+ IASTNameOwner.r_definition) + IASTNameOwner.r_reference) + IASTNameOwner.r_unclear;
	
	static final String MAIN_FUNCTION_NAME = "main";
	
	public static final List<Class<? extends Exception>> DEFAULT_EXCEPTION = Arrays.asList(Exception.class);
	public static final List<Class<? extends Exception>> AST_EXCEPTION = Arrays.asList(ASTException.class);

	@SuppressWarnings("unchecked")
	public static final Class<IASTNode>[] 				AST_NODE = new Class[] {
			IASTNode.class};
	@SuppressWarnings("unchecked")
	public static final Class<IASTComment>[] 			AST_COMMENT = new Class[] {
			IASTComment.class};
	@SuppressWarnings("unchecked")
	public static final Class<IASTPreprocessorPragmaStatement>[] AST_PRAGMA = new Class[] {
			IASTPreprocessorPragmaStatement.class};
	@SuppressWarnings("unchecked")
	public static final Class<IASTInitializerClause>[] 	AST_INIT_CLAUSE_TYPE = new Class[] {
			IASTInitializerClause.class};
	@SuppressWarnings("unchecked")
	public static final Class<IASTExpression>[] 		AST_EXPRESSION = new Class[] {
			IASTExpression.class};
	@SuppressWarnings("unchecked")
	public static final Class<IASTIdExpression>[] 		AST_ID_EXPRESSION = new Class[] {
			IASTIdExpression.class};
	@SuppressWarnings("unchecked")
	public static final Class<IASTFunctionCallExpression>[] AST_FUNCTION_CALL_EXPRESSION = new Class[] {
			IASTFunctionCallExpression.class};
	@SuppressWarnings("unchecked")
	public static final Class<IASTFunctionDefinition>[] AST_FUNCTION_DEFINITION = new Class[] {
			IASTFunctionDefinition.class};
	@SuppressWarnings("unchecked")
	public static final Class<IASTStatement>[] 			AST_STATEMENT_TYPE = new Class[] {
			IASTStatement.class};
	@SuppressWarnings("unchecked")
	public static final Class<IASTIfStatement>[] 		AST_IF_TYPE = new Class[] {
			IASTIfStatement.class};
	@SuppressWarnings("unchecked")
	public static final Class<IASTForStatement>[] 		AST_FOR_TYPE = new Class[] {
			IASTForStatement.class};
	@SuppressWarnings("unchecked")
	public static final Class<IASTStatement>[] 			AST_BRANCH_TYPES = new Class[] {
			IASTCaseStatement.class, IASTDefaultStatement.class, IASTDoStatement.class, 
			IASTForStatement.class, IASTIfStatement.class, IASTWhileStatement.class};
	@SuppressWarnings("unchecked")
	public static final Class<IASTStatement>[] 			AST_LOOP_TYPES = new Class[] {
			IASTDoStatement.class, IASTForStatement.class, IASTWhileStatement.class};
	@SuppressWarnings("unchecked")
	public static final Class<IASTArraySubscriptExpression>[] 	AST_ARRAY_SUB_TYPE = new Class[] {
			IASTArraySubscriptExpression.class};
	@SuppressWarnings("unchecked")
	public static final Class<IASTNode>[] 				AST_ASSIGNMENT_TYPES = new Class[] {
			IASTUnaryExpression.class, IASTBinaryExpression.class, IASTEqualsInitializer.class};

	
	
	private static final Map<IPath, IASTTranslationUnit> 		TU_CACHE = new HashMap<>();
	private static final Map<IASTTranslationUnit, List<IASTPreprocessorPragmaStatement>>	
	PRAGMA_CACHE = new HashMap<>();

	private static final DuoKeyMap<IASTNode, Class<? extends IASTNode>[], List<? extends IASTNode>> 
	ANCESTORS_CACHE = new DuoKeyMap<>();
	private static final DuoKeyMap<IASTNode, Class<? extends IASTNode>, List<? extends IASTNode>> 
	DESCENDANTS_CACHE = new DuoKeyMap<>();

	private static final Map<IName, IASTName> 					
	AST_NAME_CACHE 			= new HashMap<>();
	private static final DuoKeyMap<IBinding, Integer, IASTName> 					
	BINDING_NAME_CACHE 			= new DuoKeyMap<>();

	private static final Map<IName, IFunction> 					FUNCTION_CACHE 			= new HashMap<>();
	private static final Map<IASTNode, IASTFunctionDefinition>	WRITING_FUNCTION_CACHE 	= new HashMap<>();
	private static final Map<IASTFunctionDefinition, Boolean> 	GROUND_FUNCTION_CACHE 	= new HashMap<>();
	
	private static final DuoKeyMap<IASTIfStatement, IASTIfStatement, Boolean> 	
	IS_ELSE_TO_CACHE 	= new DuoKeyMap<>();

	// TODO: caching all reusable utility method results

	private static ICProject selectedProj = null;

	private static IIndex index = null;

	
	
	public static IIndex getIndex(boolean refreshesIndex) {
		if (index == null || refreshesIndex)
			try {
				index = CCorePlugin.getIndexManager().getIndex(
						CoreModel.getDefault().getCModel().getCProjects(), 
						IIndexManager.ADD_DEPENDENCIES | IIndexManager.ADD_DEPENDENT);
			} catch (CoreException e) {
				DebugElement.throwTodoException("CDT exception", e);
			}
		return index;
	}

	public static IASTTranslationUnit getAST(IPath tuPath, boolean refreshesIndex) {
		if (tuPath == null) return null;
		
		// CoreModelUtil.findTranslationUnit(IFile) always return null!
//		TU_CACHE.clear();
		IASTTranslationUnit astTu = TU_CACHE.get(tuPath);
		if (astTu == null) {
			ITranslationUnit tu;
			try {
				tu = CoreModelUtil.findTranslationUnitForLocation(
						tuPath, selectedProj);
				if (tu == null) return null;
				else TU_CACHE.put(tuPath, astTu = tu.getAST());
//					astTu = tu.getAST(index, ITranslationUnit.AST_SKIP_ALL_HEADERS));
			} catch (CoreException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

		// TODO: automatic refreshing index on index-rebuilt exceptions
//			return tu.getAST(getIndex(refreshesIndex), ITranslationUnit.AST_SKIP_INDEXED_HEADERS);
//		return tu.getAST(
//				getIndex(false), ITranslationUnit.AST_SKIP_INDEXED_HEADERS);
		return astTu;
	}

	public static Collection<IASTTranslationUnit> getRegisteredAST() {
		return TU_CACHE.values();
	}
	

	
	public static List<IASTPreprocessorPragmaStatement> getPragmas(IASTTranslationUnit tu) {
		if (tu == null) return Collections.<IASTPreprocessorPragmaStatement>emptyList();
		
//		PRAGMA_CACHE.clear();
		List<IASTPreprocessorPragmaStatement> ps = PRAGMA_CACHE.get(tu);
		if (ps != null) return ps;
		
		ps = new ArrayList<>();
		for (IASTPreprocessorStatement p : tu.getAllPreprocessorStatements())
			// ps.getParent() returns IASTTranslationUnit
			if (AST_PRAGMA[0].isInstance(p)) ps.add((IASTPreprocessorPragmaStatement) p); 
		PRAGMA_CACHE.put(tu, ps);
		return ps;
	}
	
	/**
	 * @param project
	 */
	public static void setSelectedProject(IProject project) {
		ICProject cProj = CoreModel.getDefault().getCModel().getCProject(project.getName());
		if (cProj == null) throw new IllegalArgumentException("ONLY supporting C/C++ projects!");
		selectedProj = cProj;
	}



	/**
	 * @param func
	 * @return
	 */
	public static boolean isMainFunction(IASTFunctionDefinition func) {
		return func.getDeclarator().getName().toString().equals(MAIN_FUNCTION_NAME);
	}
	
	public static boolean isGround(IASTFunctionDefinition func) {
		if (func == null) return false;
		
		Boolean isGround = GROUND_FUNCTION_CACHE.get(func);
		if (isGround != null) return isGround;
		
		isGround = getFirstDescendantOfAs(func, AST_FUNCTION_CALL_EXPRESSION[0]) == null;
		GROUND_FUNCTION_CACHE.put(func, isGround);
		return isGround;
	}


	
	/**
	 * @param exp
	 * @return true for the null expression.
	 */
	public static boolean isConstant(IASTExpression exp) {
		if (exp == null) return true;
		if (exp instanceof IASTLiteralExpression) return isConstant((IASTLiteralExpression) exp);
		if (exp instanceof IASTUnaryExpression) return isConstant((IASTUnaryExpression) exp);
		if (exp instanceof IASTBinaryExpression) return isConstant((IASTBinaryExpression) exp);
		DebugElement.throwTodoException(toStringOf(exp));
		return false;
	}
	
	public static boolean isConstant(IASTLiteralExpression exp) {
		return true;
	}
	
	public static boolean isConstant(IASTUnaryExpression exp) {
		if (exp == null) return true;
		return isConstant(exp.getOperand());
	}
	
	public static boolean isConstant(IASTBinaryExpression exp) {
		if (exp == null) return true;
		return isConstant(exp.getOperand1()) && isConstant(exp.getOperand2());
	}


	
	public static boolean isGlobal(IName name) {
		return name != null && isGlobal(toASTName(name));
	}
	
	public static boolean isGlobal(IASTName name) {
		if (name == null) throwNullArgumentException("variable name");
		
		final IBinding bind = getBindingOf(name);
		try {
			return bind.getScope().getKind().equals(EScopeKind.eGlobal);
			
		} catch (DOMException e) {
			return throwASTException(bind, e);
		}
//		IASTTranslationUnit varTu = var.getTranslationUnit();	// needs IASTName to retrieve its host TU
//		return getAncestorOfAs(varTu.getDeclarationsInAST(var.resolveBinding())[0], IASTDeclarationStatement.class)
//				.getParent() == varTu;
	}

	
	
	/**
	 * @param enumType
	 * @return
	 */
	public static boolean isBinary(IEnumeration enumType) {
		if (enumType == null) return false;
		return enumType.getEnumerators().length == 2;
	}
	
	/**<pre>
	 * Relational expressions exclude shift and equality ones. They are ones with operators >, <, >= and <= ONLY.
	 * 
	 *		relational-op 	One of the following:
	 * 						<
	 * 						<=
	 * 						>
	 * 						>=
	 * <br>
	 *  
	 * @param exp
	 * @return
	 */
	public static boolean isBinaryRelation(IASTExpression exp) {
		if (exp instanceof IASTBinaryExpression) {
			int op = ((IASTBinaryExpression) exp).getOperator();
			return (op == IASTBinaryExpression.op_greaterEqual ||
					op == IASTBinaryExpression.op_greaterThan ||
					op == IASTBinaryExpression.op_lessEqual ||
					op == IASTBinaryExpression.op_lessThan);
		}
		return false;
	}


	
	public static boolean isCollocally(IASTNode node1, IASTNode node2) {
		if (node1 == null || node2 == null) throwNullArgumentException("node");
		return getWritingFunctionDefinitionOf(node1) == getWritingFunctionDefinitionOf(node2);
	}

	public static boolean isParameter(IASTName id) {
		return id.resolveBinding() instanceof IParameter;
	}
	
	
	
	public static boolean isSameIterationOf(
			final IASTNode node1, final IASTNode node2, final IASTStatement branch) {
		if (node1 == null) throwNullArgumentException("AST node 1");
		if (node2 == null) throwNullArgumentException("AST node 2");
		if (branch == null) throwNullArgumentException("AST branch node");
		
		if (branch instanceof IASTForStatement) 
			return isSameIterationOf(node1, node2, (IASTForStatement) branch);
//		else if (branch instanceof IASTWhileStatement) 
//			return branch.contains(node1) && branch.contains(node2);
		else throwTodoException("unsupported branch type");
		
		return false;
	}
	
	private static boolean isSameIterationOf(
			final IASTNode node1, final IASTNode node2, final IASTForStatement branch) {
		assert node1 != null && node2 != null && branch != null;
		final IASTStatement init = branch.getInitializerStatement();
		final boolean isInit1 = init.contains(node1), isInit2 = init.contains(node2);
		if (isInit1) return isInit2;
		if (isInit2) return isInit1;
		
		final IASTExpression cond = branch.getConditionExpression(), iter = branch.getIterationExpression();
		final boolean isCond1 = cond.contains(node1), isCond2 = cond.contains(node2),
				isIter1 = iter.contains(node1), isIter2 = iter.contains(node2);
		if (isCond1 || isIter1) return isCond2 || isIter2;
		if (isCond2 || isIter2) return isCond1 || isIter1;
		// as usual body containment finally
		return isSameStatementOf(node1, node2, branch.getBody());
	}
	
	private static boolean isSameStatementOf(
			final IASTNode node1, final IASTNode node2, final IASTStatement stat) {
		assert stat != null;
		return stat.contains(node1) && stat.contains(node2);
	}
	
	public static boolean isSameBranchOf(
			final IASTNode node1, final IASTNode node2, final IASTStatement branch) {
		if (node1 == null) throwNullArgumentException("AST node 1");
		if (node2 == null) throwNullArgumentException("AST node 2");
		if (branch == null) throwNullArgumentException("AST branch node");
		
		if (branch instanceof IASTIfStatement) return isSameBranchOf(node1, node2, (IASTIfStatement) branch);
		
//		IASTStatement body = null;
//		if (branch instanceof IASTForStatement) body = ((IASTForStatement) branch).getBody();
//		else if (branch instanceof IASTWhileStatement) body = ((IASTWhileStatement) branch).getBody();
//		else throwTodoException("unsupported branch type");
		
		return branch.contains(node1) && branch.contains(node2);
	}
	
	private static boolean isSameBranchOf(
			final IASTNode node1, final IASTNode node2, final IASTIfStatement branch) {
		assert node1 != null && node2 != null && branch != null;
		final IASTStatement then = branch.getThenClause(), els = branch.getElseClause();
		return (then != null && then.contains(node1) && then.contains(node2)) 
				|| (els != null && els.contains(node1) && els.contains(node2)); 
	}
	
	/**
	 * @param node1
	 * @param node2
	 * @param branch
	 * @return true when there's 1) extra-if mutex branch or 2) intra-if mutex branch
	 */
	public static boolean isMutexBranchOf(
			final IASTNode node1, final IASTNode node2, final IASTIfStatement branch) {
		if (node1 == null) throwNullArgumentException("AST node 1");
		if (node2 == null) throwNullArgumentException("AST node 2");
		if (branch == null) throwNullArgumentException("AST branch node");

		final IASTStatement then = branch.getThenClause();
		if (then == null) return false;

		final boolean thenc1 = then.contains(node1), thenc2 = then.contains(node2);
		if (thenc1 && thenc2) return false;
		
		final IASTStatement els = branch.getElseClause();
		final boolean ie = els != null, elsec1 = ie && els.contains(node1), elsec2 = ie && els.contains(node2);
		if (elsec1 && elsec2) return false; 

		// !thenc2 && (elsec2:intra-if || !elsec2:extra-if)
		// !thenc1 && (elsec1:intra-if || !elsec1:extra-if)
		if (thenc1 || thenc2) return true;	
		
		// !thenc1 && !thenc2 && extra-if
		return !(!elsec1 && !elsec2); 
	}

	public static boolean isElse(IASTStatement stat) {
		if (stat == null) return false;
		
		IASTIfStatement parIf = getAncestorOfAs(stat, AST_IF_TYPE, true);
		if (parIf == null) return false;
		
		return parIf.getElseClause() == stat;
	}
	
	public static boolean isElseOf(final IASTNode node, final IASTIfStatement ifStat) {
		if (node == null || ifStat == null) return false;
		
		final IASTStatement parent = getAncestorOfAs(node, AST_STATEMENT_TYPE, true);
		if (parent == null) return false;
		if (parent == ifStat.getElseClause()) return true;
		return isElseOf(parent.getParent(), ifStat);
	}
	
	public static boolean isElseTo(IASTNode node1, IASTNode node2) {
		final IASTIfStatement if1 = getAncestorOfAs(node1, AST_IF_TYPE, true),
				if2 = getAncestorOfAs(node2, AST_IF_TYPE, true);
		return if1 == if2 ? isElseOf(node1, if1) : isElseTo(if1, if2);
	}
	
//	public static boolean isElseTo(IASTStatement stat1, IASTStatement stat2) {
//		return isElseTo(stat1 instanceof IASTIfStatement ? 
//				(IASTIfStatement) stat1 : getAncestorOfAs(stat1, AST_IF_TYPE, false), 
//				stat2 instanceof IASTIfStatement ? 
//				(IASTIfStatement) stat2 : getAncestorOfAs(stat2, AST_IF_TYPE, false));
//	}
	
	public static boolean isElseTo(IASTIfStatement if1, IASTIfStatement if2) {
		if (if1 == null || if2 == null) return false;
		if (if1 == if2) return false;
		
		Boolean isET = IS_ELSE_TO_CACHE.get(if1, if2);
		if (isET == null) { 
			if (if1.contains(if2)) isET = containsElseTo(if1, if2);
			else if (if2.contains(if1)) isET = containsElseTo(if2, if1);
			else isET = false;

//			// Ancestor {@code if2} traversal first, then descendant {@code if2} traversal.
//			// Ancestor if2 traversal
//			if (isElseTo(if1, getAncestorOfAs(if2, AST_IF_TYPE, false))) {
//				isET = true; break computeIsET;}
//			
//			// descendant if2 traversal - avoiding if2d -> if2d's ancestor -> if2d ...
			
			IS_ELSE_TO_CACHE.put(if1, if2, isET);
		}
		return isET;
	}
	
	private static boolean containsElseTo(IASTIfStatement if1, IASTIfStatement if2) {
		assert if1 != null && if2 != null && if1.contains(if2);
		final IASTStatement if1else = if1.getElseClause();
		if (if1else == null) return false;
		if (if1else == if2) return true;
		
		for (IASTIfStatement if1d : getDescendantsOfAs(if1else, AST_IF_TYPE[0]))
			if (if1d == if2) return true; 
		return false;
	}
	
	
	
	public static boolean dependsOn(IASTFunctionDefinition f1, IASTFunctionDefinition f2) {
		if (f1 == null || f2 == null) return false;
		if (isGround(f1)) return false;
		
		final IASTName f2n = getNameOf(f2);
		for (IASTFunctionCallExpression call : 
			getDescendantsOfAs(f1, AST_FUNCTION_CALL_EXPRESSION[0])) 
			if (equals(f2n, getEnclosingFunctionCallNameOf(call))) return true;
		return false;
	}
	
	public static boolean dependsOnElseTo(IASTNode node1, IASTNode node2) {
		return isElseTo(node1, node2);
		
//		final IASTIfStatement if1 = getAncestorOfAs(node1, AST_IF_TYPE, true),
//				if2 = getAncestorOfAs(node2, AST_IF_TYPE, true);
//		return if1 == if2 ? isElseOf(node1, if1) : isElseTo(if1, if2);
	}
	

	
	/**
	 * @param descend
	 * @param stopTypes - the inclusive stop types during traversing 
	 * ancestors
	 * @return A descendant-inclusive ancestor list.
	 */
	@SuppressWarnings("unchecked")
	public static <StopAncestor extends IASTNode> List<IASTNode> 
	getAncestorsOfUntil(IASTNode descend, Class<StopAncestor>[] stopTypes) {
		if (descend == null) return null;
//		if (descend == null) return throwNullArgumentException("descendant node");
		
		List<IASTNode> ancestors = 
				(List<IASTNode>) ANCESTORS_CACHE.get(descend, stopTypes);
		
		if (ancestors == null) {
			traverseAncestors: {
			if (stopTypes != null) 
				for (Class<StopAncestor> stopType : stopTypes) 
					if (stopType.isInstance(descend)) 
						break traverseAncestors;
			
			ancestors = getAncestorsOfUntil(getParentOf(descend), stopTypes);
			}

			ancestors = ancestors == null 
					? new ArrayList<IASTNode>() 
					: new ArrayList<IASTNode>(ancestors);
			ancestors.add(0, (StopAncestor) descend);
			ANCESTORS_CACHE.put(descend, stopTypes, ancestors);
		}
		
		return ancestors;
	}

	/**
	 * @param descend
	 * @param ancestorTypes
	 * @return the closest ancestor of descend (either inclusively or 
	 * exclusively) 
	 * 	in one of ancestorTypes. 
	 */
	public static <Ancestor extends IASTNode> Ancestor getAncestorOfAs(
			IASTNode descend, Class<Ancestor>[] ancestorTypes, Boolean includesDescend) {
		return getAncestorOfAsUnless(
				descend, ancestorTypes, null, includesDescend);
	}
	
	/**
	 * @param descend
	 * @param ancestorTypes
	 * @param stopTypes
	 * @param includesDescend
	 * @return the closest ancestor of descend (exclusively) in one of ancestorTypes. 
	 */
	@SuppressWarnings("unchecked")
	public static <Ancestor extends IASTNode, StopAncestor extends IASTNode> 
	Ancestor getAncestorOfAsUnless(IASTNode descend, Class<Ancestor>[] ancestorTypes,
			Class<StopAncestor>[] stopTypes, Boolean includesDescend) {
		if (descend == null || ancestorTypes == null) 
			return null;
//			return throwNullArgumentException("descendant node");

		if (includesDescend == null) {
			Class<?> dc = descend.getClass();
			for (Class<?> ac : ancestorTypes) try {
				includesDescend = dc.asSubclass(ac) != null;
			} catch (ClassCastException e) {
				includesDescend = false;
			}
		}
		List<IASTNode> ans = getAncestorsOfUntil(descend, stopTypes);	// inclusive ancestors
		for (IASTNode a : ans.subList(includesDescend ? 0 : 1, ans.size())) 
			for (Class<Ancestor> at : ancestorTypes) 
				if (at.isInstance(a)) return (Ancestor) a;
		
		return null;
		
//		traverseParents: {	
//			IASTNode ancestor = descend.getParent();
//			while (ancestor != null) {
//				if (ancestorTypes != null) 
//					for (Class<Ancestor> ancestorType : ancestorTypes) 
//						if (ancestorType.isInstance(ancestor)) 
//							break traverseParents;
//				if (stopTypes != null) 
//					for (Class<? extends IASTNode> stopType : stopTypes) 
//						if (stopType.isInstance(ancestor)) 
//							return null;
//				ancestor = ancestor.getParent();
//			}
//		}
//		return (Ancestor) ancestor;
	}
	
	public static IASTInitializerClause getAncestorClauseOf(
			final IASTNode descend, final boolean includesDescend) {
		return getAncestorOfAs(descend, ASTUtil.AST_INIT_CLAUSE_TYPE, includesDescend);
	}
			
	public static <Ancestor extends IASTNode> int getContinuousAncestorsCountOf(
			IASTNode descend, Class<Ancestor> ancestorType) {
		int count = 0;	// TODO: caching count
		boolean isContinuous = true;
		IASTNode ancestor = descend;
		
		while (ancestor != null && isContinuous) 	// descend may be null
			if (ancestorType.isInstance(ancestor)) {
				count++;
				ancestor = getParentOf(ancestor);
			} else isContinuous = false;
		
		return count;
	}

	@SuppressWarnings("unchecked")
	public static <Descendant extends IASTNode> Iterable<Descendant> getDescendantsOfAs(
			IASTNode ancestor, Class<Descendant> descendType) {
		if (ancestor == null) return null;
		
		List<Descendant> descendants = 
				(List<Descendant>) DESCENDANTS_CACHE.get(ancestor, descendType);
		if (descendants != null) return descendants;
		
		descendants = new ArrayList<Descendant>();
		for (IASTNode child : ancestor.getChildren()) if (child != null) {
			if (descendType.isInstance(child)) descendants.add((Descendant) child);
			descendants.addAll(
					(Collection<? extends Descendant>) getDescendantsOfAs(child, descendType));
		}
		DESCENDANTS_CACHE.put(ancestor, descendType, descendants);
		return descendants;
	}
	
	@SuppressWarnings("unchecked")
	public static <Descendant extends IASTNode> Descendant getFirstDescendantOfAs(
			IASTNode ancestor, Class<Descendant> descendType) {
		// TODO: caching the first descendant
		if (ancestor == null) return null;
		
		for (IASTNode child : ancestor.getChildren())
			if (child != null)
				if (descendType.isInstance(child)) return (Descendant) child;
				else {
					Descendant descend = getFirstDescendantOfAs(child, descendType);
					if (descend != null) return descend;
				}
		
		return null;
	}
	
	public static IASTNode getLastDescendantOf(IASTNode ancestor) {
		// TODO: caching the last descendant
		if (ancestor == null) return null;
		
		final IASTNode[] children = ancestor.getChildren();
		if (children == null) return ancestor;
		final int childSize = children.length;
		if (childSize <= 0) return ancestor;
		return getLastDescendantOf(children[childSize - 1]);
	}
	
	
	
	public static IASTNode getParentOf(final IASTNode descend) {
		if (descend == null) throwNullArgumentException("descendant");
		return descend instanceof IASTPreprocessorPragmaStatement
				? getParentOf((IASTPreprocessorPragmaStatement) descend)
				: descend.getParent();
	}
	
	public static IASTNode getParentOf(final IASTPreprocessorPragmaStatement descend) {
		if (descend == null) throwNullArgumentException("descendant");
		
		final IASTFileLocation l = descend.getFileLocation();
		return descend.getTranslationUnit().getNodeSelector(null).findEnclosingNode(
				l.getNodeOffset() - 1, l.getNodeLength() + 1);
	}
	
	public static IASTStatement getParentBranchOf(IASTNode descend) {
		return getAncestorOfAs(descend, ASTUtil.AST_BRANCH_TYPES, false);
	}
	
//	/**
//	 * @param me
//	 * @param start
//	 * @param length
//	 * @param tu
//	 * @param ns
//	 * @return the direct biggest small sibling node of {@code me} in AST.
//	 */
//	private static IASTNode previousOfContained(final IASTNode me, 
//			final int[] start, final int[] length, 
////			final boolean includesPragma, 
//			final IASTTranslationUnit tu, final IASTNodeSelector ns) {
//		assert me != null && start != null && start.length > 0 
//				&& length != null && length.length > 0 && tu != null && ns != null;
//		
//		IASTNode pre = null;
//		while (start[0] > 0) {
//			// TODO: binary search: start[0]-=2n, length[0]+=2n
//			pre = ns.findFirstContainedNode(start[0]--, length[0]++);
//			if (pre != null) break;
//		}
//
////		if (includesPragma) pre = previousPragmaOfAfter(me, pre, tu);
//		return pre;
//	}
	

	
	public static Iterable<IASTName> getIdsUsedBy(IASTExpression exp) {
		return getDescendantsOfAs(exp, IASTName.class);
	}

	public static int countNamesOfIn(IASTName name, IASTNode root) {
		if (name == null || root == null) return 0;
		
		final ASTNameCollector nc = new ASTNameCollector(name.getSimpleID());
		root.accept(nc);
		final IASTName[] names = nc.getNames();	// TODO: caching count?
		return names == null ? 0 : names.length;
	}
	
	public static <Descendant extends IASTNode> int countDirectContinuousDescendantsOf(
			IASTNode ancestor, Class<Descendant> descendType) {
		if (ancestor == null) return 0;
		
		int count = 0;	// TODO: caching count
		for (IASTNode child : ancestor.getChildren())
			if (child != null && descendType.isInstance(child))
				count += (1 + countDirectContinuousDescendantsOf(child, descendType));
		
		return count;
	}
	
	/**
	 * @param descend
	 * @param ancestor - a descendant-inclusive ancestor
	 * @param ancestors - a pre-cached ancestor list if available
	 * @return
	 */
	public static boolean hasAncestorAs(
			IASTNode descend, IASTNode ancestor, List<IASTNode> ancestors) {
		if (descend == null || ancestor == null) return false;
		if (descend == ancestor) return true;	// excluding the null case above
		
		int ancestorsSize;
		// case of descend == ancestors[0] == ancestor
		if (ancestors != null && descend == ancestors.get(0)) {
			ancestorsSize = ancestors.size();
			if (ancestorsSize > 1)
				for (IASTNode anc : ancestors.subList(1, ancestorsSize)) 
					if (anc == ancestor) return true; 
		}

		// resolving ancestors if no valid cache available
		ancestors = getAncestorsOfUntil(descend, null);
		
		// excluding the already handled case of descend == ancestors[0] == ancestor
		if (ancestors != null) {
			ancestorsSize = ancestors.size();
			if (ancestorsSize > 1) 
				for (IASTNode anc : ancestors.subList(1, ancestorsSize)) 
					if (anc == ancestor) return true; 
		}
		return false;
	}
	


	
	
	
	
//	public static int getDeclaredDim(IASTArraySubscriptExpression array) {
//		findDeclaration(((IASTIdExpression) array.getArrayExpression()).getName());
//		return 0;
//	}
	
	
	
	public static IName getDefinitionOf(IASTName name) {
		if (name == null) return null;
		
		// Searching for local definition first
		IName[] defs = 
				name.getTranslationUnit().getDefinitions(name.resolveBinding());
		if (defs != null && defs.length > 0) return defs[0];
		
		// Searching for global definition
		IIndex index = getIndex(false);
		try {
			index.acquireReadLock();
			// IIndex doesn't find names for IParameter's
//			defs = index.findNames(
//					name.resolveBinding(), IIndex.FIND_ALL_OCCURRENCES);	// internal NullPointerException!
			for (IIndexBinding bind : index.findBindings(
					name.toCharArray(), IndexFilter.ALL, new NullProgressMonitor())) {
				defs = index.findReferences(bind);
				if (defs != null && defs.length > 0) return defs[0];
			}
		} catch (InterruptedException | CoreException e) {
			DebugElement.throwTodoException(e.toString());
		} finally {
			index.releaseReadLock();
		}
		return null;
	}
	
	public static IASTFunctionDefinition getDefinitionOf(IFunction f) {
		if (f == null) DebugElement.throwNullArgumentException("function");

		for (IASTName n : getNameOf(f)) {
			final IASTFunctionDefinition d = getWritingFunctionDefinitionOf(n);
			// excluding function calls
//			if (d != null && getNameOf(d).resolveBinding().equals(f)) 
			if (d != null && Elemental.tests(()->
			getNameOf(d).resolveBinding().toString().equals(f.toString()))) 
				return d;	
		}
		return null;
//		return getWritingFunctionDefinitionOf(getNameOf(f, IASTNameOwner.r_definition));
	}
	
	public static IBinding getBindingOf(IName name) {
		if (name == null) throwNullArgumentException("name");
		
		IBinding bind = null;
		if (name instanceof IASTName) {
			final IASTName astName = (IASTName) name;
			bind = astName.resolveBinding();
			if (bind == null || bind instanceof IProblemBinding) {
				if (astName.isFrozen()) throwTodoException(bind.toString());
//					ASTUtil.throwASTException(idBind, null);
				else {
//					idExp = (IASTIdExpression) idExp.getOriginalNode();
//					if (idExp == null) throwNullArgumentException("frozen id expression");
//					name = idExp.getName();
					bind = ((IASTName) astName.getOriginalNode()).resolveBinding();
				}
			}
			return bind;	// this won't throw CoreException! 
		}

		IIndex index = getIndex(false);
		// read-lock pattern on the IIndex
		try {
			index.acquireReadLock();
			bind = index.findBinding(name);
		} catch (CoreException | InterruptedException e) {
			throwTodoException(e);
		} finally {
			index.releaseReadLock();
		}
		return bind;
	}
	
//	@SuppressWarnings("unchecked")
//	public static <T extends IASTNode> T getFrozenOriginalNodeOf(T copy) {
//		if (copy == null) return copy;
//		
//		final T ori = (T) copy.getOriginalNode();
//		if (copy.isFrozen()) return ori;
//		
//		// non-frozen copy
//		final IASTNode oriParent = getFrozenOriginalNodeOf(copy.getParent());
//		if (oriParent == null) return ori;
//		for (IASTNode child : oriParent.getChildren()) {
//			if (child.equals(copy)) return (T) child.getOriginalNode();
//		}
//		return DebugElement.throwTodoException("unsupported copy");
//	}
	
	/**
	 * @param fName - the name of function to search for
	 * @return
	 */
	public static IFunction getFunctionBindingOf(IName fName) {
		if (fName == null) return null;
		
		IBinding fBind = getBindingOf(fName);
		if (fBind instanceof IFunction) return (IFunction) fBind;
		
//		f = fbind.getAdapter(IFunction.class);	// IIndexBinding has NO adapters for IFunction!
		IFunction f = FUNCTION_CACHE.get(fName);
		if (f == null) {
			final IASTName fASTName = toASTName(fName);
			if (fASTName != null) {
				fBind = fASTName.resolveBinding();
				if (fBind instanceof IFunction) FUNCTION_CACHE.put(fName, f = (IFunction)fBind); 
			}
		}
		return f;
	}

	public static IASTFunctionDefinition getWritingFunctionDefinitionOf(IASTNode node) {
		if (node == null) throwNullArgumentException("node");
		if (node instanceof IASTFunctionDefinition) return (IASTFunctionDefinition) node;
		
		IASTFunctionDefinition def = WRITING_FUNCTION_CACHE.get(node);
		if (def == null) WRITING_FUNCTION_CACHE.put(
				node, 
				def = (IASTFunctionDefinition) getAncestorOfAs(
						node, AST_FUNCTION_DEFINITION, false));
		return def;
	}

	
	
	public static IASTFunctionCallExpression getEnclosingFunctionCallOf(IASTNode node) {
		return getAncestorOfAsUnless(
				node, AST_FUNCTION_CALL_EXPRESSION, AST_STATEMENT_TYPE, true);
	}
	
	public static IASTName getEnclosingFunctionCallNameOf(IASTFunctionCallExpression call) {
		if (call == null) throwNullArgumentException("call");
		
		IASTExpression callNameExp = call.getFunctionNameExpression();
		if (callNameExp instanceof IASTIdExpression) 
			return ((IASTIdExpression) callNameExp).getName();
		// TODO: else if ...
		return null;
	}
	
	public static IASTName getEnclosingFunctionCallNameOf(IASTNode node) {
		// call != null -> call instanceof IASTFunctionCallExpression
		return getEnclosingFunctionCallNameOf(getEnclosingFunctionCallOf(node));
	}
	
	

	/**<pre>
	 * Retrieving the direct parent loop within the same function definition.
	 * </pre>
	 * 
	 * @param node
	 * @return
	 */
	public static IASTForStatement getEnclosingForOf(IASTNode node) {
		return getAncestorOfAsUnless(
				node, 
				AST_FOR_TYPE,
				AST_FUNCTION_DEFINITION, 
				false);
	}
	
	/**<pre>
	 * Retrieving the direct parent loop within the same function definition.
	 * 
	 * Only supporting the OpenMP canonical for-loop 
	 * ({@linkplain OpenMP ﻿http://www.openmp.org/mp-documents/openmp-4.5.pdf}).
	 * 
	 * TODO: getEnclosingLoopCondition(...) for handling break/continue statements and while-loop conditions.
	 * <br>
	 * 
	 * @param innerLoop
	 * @return
	 */
	public static IASTForStatement getEnclosingForOf(final IASTForStatement innerLoop) {
		return getAncestorOfAsUnless(
				innerLoop, 
				AST_FOR_TYPE,
				AST_FUNCTION_DEFINITION, 
				false);
	}
	
//	/**
//	 * @param conditionalStatement - supposed to be a conditional (branching) statement, 
//	 * 	which is one of {@link IASTCaseStatement}, {@link IASTDefaultStatement}, 
//	 * 	{@link IASTDoStatement}, {@link IASTForStatement}, {@link IASTIfStatement} and 
//	 * 	{@link IASTWhileStatement} 
//	 * @return
//	 */
//	public static IASTExpression getConditionExpressionOf(IASTStatement conditionalStatement) {
//		if (conditionalStatement == null) return null;
//		
//		if (conditionalStatement instanceof IASTCaseStatement)
//			return ((IASTCaseStatement) conditionalStatement).getExpression();
//		if (conditionalStatement instanceof IASTDefaultStatement)
//			return ((IASTDefaultStatement) conditionalStatement).get;
//		if (conditionalStatement instanceof IASTDoStatement)
//			return ((IASTDoStatement) conditionalStatement).getExpression();
//		if (conditionalStatement instanceof IASTForStatement)
//			return ((IASTForStatement) conditionalStatement).getExpression();
//		if (conditionalStatement instanceof IASTIfStatement)
//			return ((IASTIfStatement) conditionalStatement).getExpression();
//		if (conditionalStatement instanceof IASTWhileStatement)
//			return ((IASTWhileStatement) conditionalStatement).getExpression();
//		return null;
//	}
	


	public static IASTIfStatement getEnclosingIfStatementOf(IASTNode node) {
		if (node == null) DebugElement.throwNullArgumentException("AST node");
		return (IASTIfStatement) getAncestorOfAs(
				node, AST_IF_TYPE, true);
	}
	
	@SuppressWarnings("unchecked")
	public static IASTSwitchStatement getEnclosingSwitchStatementOf(IASTStatement stat) {
		if (stat == null) DebugElement.throwNullArgumentException("AST statement");
		return (IASTSwitchStatement) getAncestorOfAs(
				stat, new Class[] {IASTSwitchStatement.class}, true);
	}
	

	
	public static IASTArraySubscriptExpression getEnclosingArraySubscriptOf(
			final IASTNode node) {
		return getAncestorOfAsUnless(
				node, 
				AST_ARRAY_SUB_TYPE,
				AST_STATEMENT_TYPE, 
				true);
	}
	
	/**
	 * @param node
	 * @return @NotNull list.
	 */
	public static List<IASTArraySubscriptExpression> getEnclosingArraySubscriptsOf(final IASTNode node) {
		final List<IASTArraySubscriptExpression> enclosings = new ArrayList<>();
		final List<IASTNode> ancs = getAncestorsOfUntil(node, AST_STATEMENT_TYPE);
		for (IASTNode anc : ancs) 
			if (anc instanceof IASTArraySubscriptExpression) enclosings.add((IASTArraySubscriptExpression) anc);
		return enclosings;
	}
	
	
	
	@SuppressWarnings("unchecked")
	public static IASTReturnStatement getEnclosingReturnStatementOf(IASTNode node) {
		if (node == null) DebugElement.throwNullArgumentException("AST node");
		return (IASTReturnStatement) getAncestorOfAs(
				node, new Class[] {IASTReturnStatement.class}, true);
	}
	
	public static List<IASTReturnStatement> getReturnStatementsOf(IASTNode node) {
		return new ASTReturnVisitor().findIn(node);
	}
	
	public static IASTReturnStatement nextReturnStatementTo(IASTNode node) {
		return new ASTReturnVisitor().findNextTo(node);
	}
	
	private static class ASTReturnVisitor extends ASTGenericVisitor {
		private boolean hasFoundNode = false;
		private boolean findsIn = false;
		private boolean findsNextTo = false;
		private IASTNode n = null;
		final private List<IASTReturnStatement> rs = new ArrayList<>();
		
		public ASTReturnVisitor() {
			super(true);
			shouldVisitStatements = true;
		}

		public List<IASTReturnStatement> findIn(IASTNode node) {
			if (node == null) DebugElement.throwNullArgumentException("AST node");
			
			final IASTFunctionDefinition f = getWritingFunctionDefinitionOf(node);
			if (f == null) DebugElement.throwNullArgumentException("function child");
			findsIn = true; n = node;
			f.accept(this);
			return rs;
		}
		
		public IASTReturnStatement findNextTo(IASTNode node) {
			if (node == null) DebugElement.throwNullArgumentException("AST node");
			
			final IASTFunctionDefinition f = getWritingFunctionDefinitionOf(node);
			if (f == null) return null;		// node is global
			
			findsNextTo = true; n = node;
			f.accept(this);
			return rs.isEmpty() ? null : rs.get(0);
		}
		
		@Override
		protected int genericVisit(IASTNode node) {
			if (node == n) hasFoundNode = true;
			return PROCESS_CONTINUE;	// continue-ing to find r
		}
		
		@Override
		protected int genericLeave(IASTNode node) {
			if (findsIn && node == n) return PROCESS_ABORT;
			return PROCESS_CONTINUE;	// continue-ing to find r if findsNextTo
		}

		@Override
		public int visit(IASTStatement statement) {
			if (statement instanceof IASTReturnStatement && hasFoundNode) {
				rs.add((IASTReturnStatement) statement);
				if (findsNextTo) return PROCESS_ABORT;
			} 
			return PROCESS_CONTINUE;	// continue-ing to find n
		}
	}
	
	
	
	/**
	 * @param exp
	 * @return
	 */
	public static IASTExpression unbracket(IASTUnaryExpression exp) {
		// TODO: caching results
		IASTExpression ubExp = exp;
		if (exp.getOperator() == IASTUnaryExpression.op_bracketedPrimary) {
			ubExp = exp.getOperand();
			if (ubExp instanceof IASTUnaryExpression) return unbracket((IASTUnaryExpression) ubExp);
		}
		return ubExp;
	}
	
	
	
	public static IASTName getNameFrom(IPath tuPath, int offset, int length, boolean refreshesIndex) {
		IASTTranslationUnit ast = getAST(tuPath, refreshesIndex);
		if (ast == null) return null;
		else return ast.getNodeSelector(null).findFirstContainedName(offset, length);
//		else return ast.getNodeSelector(tuPath.toString()).findFirstContainedName(offset, length);
	}

	public static IASTName getNameFrom(IASTFileLocation loc, boolean refreshesIndex) {
		return getNameFrom(
				new Path(loc.getFileName()), 
				loc.getNodeOffset(), loc.getNodeLength(), refreshesIndex);
	}
	
	public static IASTName getNameOf(final IASTNameOwner owner) {
		if (owner == null) return null;
		
		for (IASTNode child : ((IASTNode)owner).getChildren()) 
			if (child instanceof IASTName) return (IASTName) child;
		return null;
	}
	
	/**
	 * @param exp
	 * @return
	 */
	public static IASTName getNameOf(final IASTIdExpression exp) {
		return (exp != null) ? exp.getName() : null;
	}
	
	public static IASTName getNameOf(IASTFunctionCallExpression exp) {
		return exp != null 
				? getNameOf(exp.getFunctionNameExpression()) : null;
	}

	/**
	 * @param exp
	 * @return
	 */
	public static IASTName getNameOf(final IASTExpression exp) {
		if (exp instanceof IASTIdExpression) 
			return getNameOf((IASTIdExpression) exp);
		
		else if (exp instanceof IASTFunctionCallExpression) 
			return getNameOf((IASTFunctionCallExpression) exp);
		
		else if (exp instanceof IASTUnaryExpression) 
			return getNameOf(((IASTUnaryExpression) exp).getOperand());
		
		return DebugElement.throwTodoException("unsupported expression");
	}

	public static IASTName getNameOf(IASTFunctionDefinition f) {
		if (f == null) return null;
		else return f.getDeclarator().getName();
	}
	
	/**
	 * @param bind - not for IParameter's since IIndex finds NO them
	 * @param role TODO
	 * @return
	 */
	public static IASTName getNameOf(IBinding bind, int role) throws ASTException {
		if (bind == null) DebugElement.throwNullArgumentException("binding");
		
		IASTName astName = BINDING_NAME_CACHE.get(bind, role);
		if (astName != null) return astName;
		
//		final boolean hasRole = role != r_any;
		int iRole;
		switch (role) {
		case IASTNameOwner.r_declaration:	iRole = IIndex.FIND_DECLARATIONS;		break;
		case IASTNameOwner.r_definition:	iRole = IIndex.FIND_DEFINITIONS;		break;
		case IASTNameOwner.r_reference:		iRole = IIndex.FIND_REFERENCES;			break;
		case IASTNameOwner.r_unclear:		iRole = IIndex.FIND_POTENTIAL_MATCHES;	break;
		case r_any:
		default:							iRole = IIndex.FIND_ALL_OCCURRENCES;
		}
		
		IIndex index = getIndex(false);
		try {
			index.acquireReadLock();
			
			// IIndex doesn't find names for IParameter's
			IName[] bindNames = index.findNames(bind, iRole);
			if (bindNames != null) for (IName name : bindNames) {
				astName = toASTName(name);
				if (astName != null) {
					assert astName.resolveBinding().equals(bind); break;
//					if (!hasRole || role == astName.getRoleOfName(true)) break;
				}
			}
			
		} catch (Exception e) {
			throwASTException(bind, e);
		} finally {
			index.releaseReadLock();
		}
		BINDING_NAME_CACHE.put(bind, role, astName);
		return astName;
	}
	
	public static Collection<IASTName> getNameOf(IBinding bind) {
		try {
			final Set<IASTName> names = new HashSet<>();
			Elemental.add(names, ()-> getNameOf(bind, IASTNameOwner.r_definition), AST_EXCEPTION);
			if (names.isEmpty()) Elemental.add(names, ()-> getNameOf(bind, IASTNameOwner.r_declaration), AST_EXCEPTION);
			if (names.isEmpty()) Elemental.add(names, ()-> getNameOf(bind, ASTUtil.r_any), AST_EXCEPTION);
			if (names.isEmpty()) {
				final ASTNameCollector nc = new ASTNameCollector(bind.getName());
				for (IASTTranslationUnit ast : getRegisteredAST()) {
					if (!ast.accept(nc)) DebugElement.throwTodoException("failed AST visiting");
					names.addAll(Elemental.toList(nc.getNames())); 
//					for (IASTName n : Elemental.toList(nc.getNames())) 
//						Elemental.addSkipNull(names, ()-> n, ()-> n.resolveBinding().equals(bind), AST_EXCEPTION);
				}
			}
			return names;
			
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	
	public static Collection<IASTName> getNameOf(IFunction func) {
		if (func == null) DebugElement.throwNullArgumentException("function");
		
		final Set<IASTName> names = new HashSet<>();
		final Collection<Entry<IName,IFunction>> funcs = FUNCTION_CACHE.entrySet();
		for (Entry<IName,IFunction> f : funcs) if (f.getValue().equals(func)) {
			final IName fn = f.getKey();
			if (fn instanceof IASTName) names.add((IASTName) fn);  
		}
		names.addAll(getNameOf((IBinding) func));
		return names;
	}
	
	/**
	 * @param bind - not for IParameter's since IIndex finds NO them
	 * @param scope - pre-cached scope name since both IBinding.getScope().getScopeName() and 
	 * 				IFunction.getFunctionScope().getScopeName() returns null!
	 * @return
	 */
	public static IASTName getNameOfFrom(IBinding bind, IName scope) {
		if (bind == null) DebugElement.throwNullArgumentException("binding");
		
		IASTFunctionDefinition scopeAST = 
				getWritingFunctionDefinitionOf(toASTName(scope));
		if (scopeAST != null) 
			for (IASTName descendName : getDescendantsOfAs(scopeAST, IASTName.class)) 
				if (descendName.resolveBinding().equals(bind)) return descendName;
		
		return getNameOf(bind, r_any);
	}

	public static IASTName toASTName(IName iName) {
		if (iName == null) return null;
		
		if (iName instanceof IASTName) return (IASTName) iName;
		else {
//			return getNameFrom(iName.getFileLocation(), false);
			IASTName aName = AST_NAME_CACHE.get(iName);
			if (aName == null) AST_NAME_CACHE.put(
					iName, aName = getNameFrom(iName.getFileLocation(), false));
			return aName;
		}
	}
	
	/**
	 * @param name
	 * @return
	 */
	public static String toStringOf(IASTName name) {
		if (name == null) return null;
		return name.toString() + " " + toStringOf(name.getNodeLocations());
//		return name.toString() + "\n" + toStringOf(name.getFileLocation()) + "\n";
	}

	public static String toStringOf(IASTNodeLocation... locations) {
		if (locations == null) DebugElement.throwNullArgumentException("location");
		
		String str = "";
		for (IASTNodeLocation loc : locations) 
			str += ((loc instanceof IASTFileLocation 
					? toStringOf((IASTFileLocation) loc)
					: loc.toString()) + "\n");
		return str;
	}
	
//	public static String toStringOf(IASTMacroExpansionLocation location) {
//		if (location == null) DebugElement.throwNullArgumentException("location");
//		return location.toString();
//	}
	
	public static String toStringOf(IASTFileLocation location) {
		if (location == null) return "(null)";
		
		String fName = location.getFileName(), 
				fnFolders[] = fName.split("/");
		fName = "";
		for (String fd : fnFolders) 
			fName = fd + (fName.isEmpty() ? "" : (" @ " + fName));
		return "at line " + location.getStartingLineNumber() + 
				" (~" + location.getNodeOffset() + 
				")\nof file " + fName;
	}
	
	public static String toStringOf(IASTNode node) {
		if (node == null) return "(null)";
		
		if (node instanceof IASTExpression) return ASTSignatureUtil.getExpressionString((IASTExpression)node);
				
		for (IASTNode child : node.getChildren()) {
			if (child instanceof IASTName) return toStringOf((IASTName) child);
			else return toStringOf(child.getFileLocation());
		}
		return toStringOf(node.getFileLocation());
	}
	
	public static String toLocationOf(IASTNode node) {
		if (node == null) return SystemElement.throwNullArgumentException("node");
		
		IASTFileLocation loc = node.getFileLocation();
		if (loc == null) return SystemElement.throwNullArgumentException("location");
		return loc.getStartingLineNumber() + "@" + loc;
	}
	
	public static String toLineLocationOf(IASTNode node) {
		if (node == null) return SystemElement.throwNullArgumentException("node");
		return toLineLocationOf(node.getFileLocation());
	}
	
	public static String toLineLocationOf(IASTFileLocation loc) {
		return toLineOffsetLocationOf(loc, false);
	}
	
	public static String toLineOffsetLocationOf(IASTFileLocation loc) {
		return toLineOffsetLocationOf(loc, true);
	}
	
	private static String toLineOffsetLocationOf(IASTFileLocation loc, boolean printsOffset) {
		if (loc == null) return null;
		String locPath = loc.getFileName();
		return loc.getStartingLineNumber() + "_" 
				+ (printsOffset ? loc.getNodeOffset() + "_" : "")
				+ locPath.substring(locPath.lastIndexOf(File.separator) + 1).replace('.', '_');
	}
	
	public static String toBriefingOf(IASTNode node) {
		return toStringOf(node) + "\n" + toLocationOf(node);
	}

	public static String toID(IType type) {
		if (type == null) SystemElement.throwNullArgumentException("type");
		final String t = type.toString();
		return t.replace(' ', '_').replaceAll("\\*", "pt");
	}
	
	
	
	public static boolean isInTheSameFile(IASTNode node1, IASTNode node2) {
		if (node1 == node2) return true;
		if (node1 == null || node2 == null) return false;
		
		return node1.getContainingFilename().equals(node2.getContainingFilename());
	}
	
	/**
	 * @param l1
	 * @param l2
	 * @return
	 */
	public static boolean equals(IASTFileLocation l1, IASTFileLocation l2) {
		if (l1 == l2) return true;
		if (l1 == null || l2 == null) return false;
		
		return l1.getFileName().equals(l2.getFileName()) && l1.getNodeOffset() == l2.getNodeOffset();
	}
	
	/**
	 * TODO? IASTName.equals(...) doesn't work as expected?
	 * TODO? IASTFunctionDefinition.equals(...) doesn't work as expected!
	 * 
	 * @param node1
	 * @param node2
	 * @return
	 */
	public static boolean equals(IASTNode node1, IASTNode node2) {
		if (node1 == node2) return true;
		if (node1 == null || node2 == null) return false;
		
		return equals(node1.getFileLocation(), node2.getFileLocation());
	}
	
	/**
	 * Checking binding equality ignoring AST location.
	 * 
	 * @param name1
	 * @param name2
	 * @return
	 */
	public static boolean equals(IASTName name1, IASTName name2) {
//		if (equals((IName) name1, (IName) name2, false)) return true;

		// TODO: the same IASTName's won't bind to the same IVariable's?
		IBinding bind1 = name1.resolveBinding(), bind2 = name2.resolveBinding();
		if (bind1 == null || bind2 == null) return false;
		return bind1.equals(bind2);
	}

	/**
	 * @param name1
	 * @param name2
	 * @param ignoresLocation - to ignore AST location equality or not?
	 * @return
	 */
	public static boolean equals(final IName name1, final IName name2, final boolean ignoresLocation) {
		if (name1 == name2) return true;
		if (name1 == null || name2 == null) return false;
		if (!ignoresLocation) return name1.equals(name2);
		
		// ignoresLocation - binding or string equivalence
		return name1 instanceof IASTName && name2 instanceof IASTName
				? equals((IASTName) name1, (IASTName) name2)
				: name1.toString().equals(name2.toString());
	}
	
	/**
	 * @param name
	 * @param ignoresLocation - To ignore location hash code or not?
	 * @return
	 */
	public static int hashCodeOf(IASTName name, boolean ignoresLocation) {
		if (name == null) 
			throw new IllegalArgumentException("Can't hash code of a null ASTName!");
		
		if (ignoresLocation) {
			IBinding bind = name.resolveBinding();
			if (bind != null) return bind.hashCode();
		}
		return name.hashCode();
//		IASTFileLocation loc = name.getFileLocation();
//		return loc.getFileName().hashCode() + new Integer(loc.getNodeOffset()).hashCode();
	}


	
	/**
	 * @param types1
	 * @param types2
	 * @return
	 */
	public static boolean superclasses(Class<?>[] types1, Class<?>[] types2) {
		if (types2 == null) return false;
		
		boolean is1supering2 = false;
		for (Class<?> type2 : types2) {
			is1supering2 = superclasses(types1, type2);
			if (!is1supering2) break;
		}
		return is1supering2;
	}
	
	/**
	 * @param types1
	 * @param type2
	 * @return
	 */
	public static boolean superclasses(Class<?>[] types1, Class<?> type2) {
		if (types1 == null) return false;
		
		boolean is1supering2 = false;
		for (Class<?> type1 : types1) {
			is1supering2 = superclasses(type1, type2);
			if (!is1supering2) break;
		}
		return is1supering2;
	}
	
	/**
	 * @param type1
	 * @param type2
	 * @return
	 */
	public static boolean superclasses(Class<?> type1, Class<?> type2) {
		if (type1 == null || type2 == null) return false;
		if (type1 == type2) return true;
		
		// checking super interfaces
		for (Class<?> itf2 : type2.getInterfaces()) 
			if (superclasses(type1, itf2)) return true;

		// checking super classes
		return superclasses(type1, type2.getSuperclass());
	}
	
	
	
	public static <T> T throwASTException(IASTNode node) 
			throws ASTException {
		throw new ASTException(node);
	}
	
	public static <T> T throwASTException(IBinding bind, Exception cause) 
			throws ASTException {
		throw bind instanceof IProblemBinding
		? new ASTException((IProblemBinding) bind, cause)
		: new ASTException(bind, cause);
	}

}