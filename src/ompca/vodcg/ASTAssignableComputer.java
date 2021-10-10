/**
 * 
 */
package ompca.vodcg;

import java.util.List;

import org.eclipse.cdt.core.dom.ast.ASTNameCollector;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFieldReference;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNameOwner;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.IArrayType;

import ompca.DebugElement;
import ompca.Elemental;

/**
 * Comparing runtime locations between L-value's in AST expressions.
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public final class ASTAssignableComputer {

//	private IIndex projectIndex;

//	public LValueComputer() {
//		projectIndex = projIdx;
//	}
	
	/**
	 * @param exp
	 * @param lValue
	 * @return name-equally dependent expression
	 */
	public static IASTExpression getDependentOnBy(IASTExpression exp, IASTExpression lValue) {
		if (exp != null) {
			if (ASTUtil.equals(exp, lValue)) return lValue;
			if (exp instanceof IASTIdExpression && lValue instanceof IASTIdExpression 
				&& ASTUtil.equals(((IASTIdExpression) exp).getName(), 
						((IASTIdExpression) lValue).getName(), true))
				return lValue;
			return getDependentOnBy(exp.getChildren(), lValue);
		}
		return null;
	}



	/**
	 * @param exps - assumed expressions
	 * @param lValue - assumed a variable ID that's probably used in the expressions
	 * @return
	 */
	public static IASTExpression getDependentOnBy(IASTNode[] exps, IASTExpression lValue) {
		if (exps != null) for (IASTNode exp : exps) if (exp instanceof IASTExpression) {
			IASTExpression by = getDependentOnBy((IASTExpression)exp, lValue);
			if (by != null) return by;
			else return getDependentOnBy(exp.getChildren(), lValue);
		}
		return null;
	}



	/**
	 * An ID is said to be dependent on a loop only if it's a variable ID and the variable is either 
	 * the loop iterator or an array accessed (indexed) by the iterator through 
	 * the (subscript) arguments or pointer to the array.
	 *
	 * TODO: Supporting loops more than the canonical ones.
	 * 
	 * @param lValue - assumed a variable name ID
	 * @param loop
	 * @param condGen 
	 * @return
	 */
	public static IASTExpression getDependentOnBy(
			final IASTExpression lValue, final IASTForStatement loop, final ASTAddressable dynaAddr, final VODCondGen condGen) {
		final IASTExpression li = Assignable.fromCanonicalIteratorOf(loop, dynaAddr, condGen).toASTExpression();	// loop iterator
		if (lValue.equals(li)) return li; 
	
		while (true) {
			IASTNode lvParent = lValue.getParent();
			if (lvParent == null) break;
			if (lvParent instanceof IASTExpression) {
				// or an array accessed (indexed) by the loop iterator
				// through the (subscript) arguments or pointer to the array.
				if (((IASTExpression) lvParent).getExpressionType() instanceof IArrayType) 
					return getDependentOnBy(lvParent.getChildren(), li);
			} else break;
		}
		return null;
	}



	/**
	 * @param lValue - variable probably used in some parameter to find out
	 * @return
	 */
	public static IASTInitializerClause getArgumentExpressionOf(IASTExpression lValue) {
		List<IASTNode> ancestors = ASTUtil.getAncestorsOfUntil(
				lValue, ASTUtil.AST_FUNCTION_CALL_EXPRESSION);
		if (ancestors != null) {
			int grandAncestorIndex = ancestors.size() - 1;
			if (ancestors.get(grandAncestorIndex) instanceof IASTFunctionCallExpression)
				// excluding IASTFunctionCallExpression and lValue itself
				for (int i = grandAncestorIndex - 1; i > 0; i--) {
					IASTNode ancestor = ancestors.get(i);
					if (ancestor instanceof IASTInitializerClause) 
						return (IASTInitializerClause) ancestor;
				}
		}

		return null;
	}

	public static IASTIdExpression getIdExpressionOf(IASTName name) {
		if (name == null) DebugElement.throwNullArgumentException("name");
		return Elemental.getSkipException(()-> ASTUtil.getAncestorOfAsUnless(
				name, 
				ASTUtil.AST_ID_EXPRESSION, 
				ASTUtil.AST_EXPRESSION, 
				false));	
	}
	
	public static IASTExpression getNonIdExpressionOf(IASTName name) {
		if (name == null) DebugElement.throwNullArgumentException("name");
		return Elemental.getNonNullSupplier(
				()-> (IASTExpression) getIdExpressionOf(name).getParent());	
	}
	


	/**
	 * Currently supporting l-value type expression: {@link IASTIdExpression} and 
	 * pointer in {@link IASTUnaryExpression}.
	 * 
	 * @param clause
	 * @return
	 */
	public static IASTName getVariableNameOf(
			final IASTInitializerClause clause) {
//			throws ASTException {
		if (clause == null) return null;
		
		if (clause instanceof IASTIdExpression) {
			return ((IASTIdExpression) clause).getName();
//			final IASTName vName = ((IASTIdExpression) clause).getName();
//			final IBinding vBind = vName.resolveBinding();
//			if (vBind instanceof IVariable) return vName;
//			if (vBind instanceof IProblemBinding) 
//				throw new ASTException((IProblemBinding) vBind, null);
		}
		else if (clause instanceof IASTLiteralExpression) 
			return null;
		
		else if (clause instanceof IASTUnaryExpression) 
			return getVariableNameOf(((IASTUnaryExpression) clause).getOperand());
		
		return DebugElement.throwTodoException("unsupported expression");
	}
	
	/**
	 * @param exp
	 * @return
	 */
	public static IASTNameOwner getVariableNameOwnerOf(
			final IASTIdExpression exp) 
					throws ASTException {
		return (exp != null && getVariableNameOf(exp) != null) ? exp : null;
	}
	
	/**
	 * @param exp
	 * @return
	 */
	public static IASTNameOwner getVariableNameOwnerOf(
			final IASTUnaryExpression exp) {
		return (exp != null) ? getVariableNameOwnerOf(exp.getOperand()) : null;
	}
	
	/**
	 * Currently supporting l-value type expression: {@link IASTIdExpression} and 
	 * pointer in {@link IASTUnaryExpression}.
	 * 
	 * @param clause
	 * @return
	 */
	public static IASTNameOwner getVariableNameOwnerOf(
			final IASTInitializerClause clause) 
					throws ASTException {
		if (clause == null) return null;
		
		if (clause instanceof IASTIdExpression) 
			return getVariableNameOwnerOf((IASTIdExpression) clause);
		else if (clause instanceof IASTFieldReference) 
			return (IASTFieldReference) clause;
		else if (clause instanceof IASTLiteralExpression) 
			return null;
		else if (clause instanceof IASTUnaryExpression) 
			return getVariableNameOwnerOf((IASTUnaryExpression) clause);
		else if (clause instanceof IASTArraySubscriptExpression) 
			return getVariableNameOwnerOf(((IASTArraySubscriptExpression) clause).getArrayExpression());
			
		return DebugElement.throwTodoException("unsupported clause");
	}



	public static boolean isAssignment(IASTInitializerClause clause) {
		return isUnaryAssignment(clause) || isBinaryAssignment(clause);
	}

	public static boolean isLikeAssignment(IASTInitializerClause clause) {
		return clause instanceof IASTUnaryExpression 
				&& isLikeAssignment((IASTUnaryExpression) clause);
	}
	
	public static boolean isAssignment(IASTUnaryExpression exp) {
		final IASTExpression ubExp = ASTUtil.unbracket(exp);
		return ubExp == exp 
				? isUnbracketedAssignment(exp) 
				: isAssignment(ubExp);
	}
	
	public static boolean isLikeAssignment(IASTUnaryExpression exp) {
		final IASTExpression ubExp = ASTUtil.unbracket(exp);
		return ubExp == exp 
				? isLikeUnbracketedAssignment(exp) 
				: isLikeAssignment(ubExp);
	}
	
	private static boolean isUnbracketedAssignment(IASTUnaryExpression exp) {
		if (exp instanceof IASTUnaryExpression) 
			switch (((IASTUnaryExpression) exp).getOperator()) {
			case IASTUnaryExpression.op_postFixDecr	: return true;
			case IASTUnaryExpression.op_postFixIncr	: return true;
			case IASTUnaryExpression.op_prefixDecr	: return true;
			case IASTUnaryExpression.op_prefixIncr	: return true;
			};
			return false;
	}
	
	private static boolean isLikeUnbracketedAssignment(IASTUnaryExpression exp) {
		if (exp instanceof IASTUnaryExpression) 
			switch (((IASTUnaryExpression) exp).getOperator()) {
			case IASTUnaryExpression.op_amper		: return true;	// assignment if passed-by-reference
			};
		return false;
	}
	

	
//	public static boolean isAssignmentOf(IASTFunctionCallExpression exp, Assignable asn) {
//		if (asn == null) DebugElement.throwNullArgumentException("assignable");
//		return asn.isAssignment(exp);
//	}
	
	public static boolean isAssignedIn(IASTExpression assignedExp, IASTInitializerClause clause) {
		if (!isAssignment(clause)) return false; 
		if (clause == assignedExp) return true;
		
		if (clause instanceof IASTUnaryExpression) 
			return ((IASTUnaryExpression) clause).getOperand().contains(assignedExp);
		if (clause instanceof IASTBinaryExpression) 
			return ((IASTBinaryExpression) clause).getOperand1().contains(assignedExp);
		
		return DebugElement.throwTodoException("Unsupported clause?");
	}
	
	/**
	 * @param assignedName
	 * @param clause
	 * @return
	 */
	public static boolean isAssignedIn(IASTName assignedName, IASTInitializerClause clause) {
		// A unary assignment has only one operand containing the given l-value
		return isUnaryAssignment(clause) 
//				|| isBinaryAssigningOf(clause, name)
				|| isAssignedIn(getNonIdExpressionOf(assignedName), clause);
	}
	
	public static boolean isAssigning(IASTName name) {
		return isUnaryAssignment(getNonIdExpressionOf(name)) 
				|| isBinaryAssigning(name);
	}
	
	public static boolean isAssigning(IASTInitializerClause clause) {
		return clause instanceof IASTArraySubscriptExpression;
	}
	
	public static boolean isAssigningIn(IASTExpression assigningExp, IASTInitializerClause clause) {
		return isUnaryAssignment(assigningExp) 
				|| isBinaryAssigningIn(assigningExp, clause);
	}

	
	
	/**
	 * @param lValue
	 * @param clause
	 * @return
	 */
	public static boolean isDirectlyAssignedOf(
			IASTName lValue, IASTInitializerClause clause) {
		// A unary assignment has only one operand containing the given l-value
		if (isUnaryAssignment(clause)) return true; 
		
		// usually IASTIdExpression in lhs of a direct (non-function-call) assignment
		final IASTIdExpression idExp = getIdExpressionOf(lValue);
		assert lValue != null;
		// idExp == null -> not a classical AST ID, e.g. a parameter declaration
		return idExp != null && isBinaryAssignedTo(clause, idExp);
	}
	
	public static boolean isDirectlyAssignedOf(
			IASTName lValue, IASTEqualsInitializer init) {
		@SuppressWarnings("unchecked")
		final IASTDeclarator decl = (IASTDeclarator) ASTUtil.getAncestorOfAs(
				lValue, new Class[] {IASTDeclarator.class}, false);
		return decl != null 
				&& decl.getName() == lValue 
				&& decl.getInitializer() == init;
	}
	
	/**
	 * TODO: checking if pointer + name = l-value
	 * @param lValue
	 * @param init
	 * 
	 * @return
	 */
	public static boolean isDirectlyAssignedOf(
			IASTExpression lValue, IASTEqualsInitializer init) {
		if (init == null || lValue == null) return false;
		
		IASTDeclarator decl = (IASTDeclarator) init.getParent();
//		decl.getPointerOperators();
		return ASTUtil.equals(decl.getName(), ASTUtil.getNameOf(lValue));	// node-location-aware
	}

//	/**
//	 * Meaning in the right hand side of binary assignment or subject of unary assignment.
//	 * 
//	 * @param var - assumed a variable ID
//	 * @return
//	 */
//	public static boolean isAssigning(IASTName var) {
//		return isBinaryAssigning(var) || isUnaryAssigning(var);
//	}

	public static Boolean isAssigned(IASTName ref, final ASTAddressable dynaAddr, VODCondGen condGen) {
		return Assignable.from(ref, dynaAddr, condGen).isAssigned();
	}

	/**
	 * Variable assigned means the subject reference is:
	 * 	either as a variable in the left hand side of a binary assignment or in a unary assignment,
	 * 	or as a function parameter passed by reference (in pointer type * or &).
	 *   
	 * IASTExpression.isLValue() -/-> IASTExpression.getParent() is an assignment
	 * 
	 * @param lvExp - the subject variable/parameter reference in a valid l-value expression,
	 * 	already bypassed IASTIdExpression 
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public static boolean isAssigned(IASTExpression lvExp) {
		if (lvExp == null) return false;
		
		// isLValue() does NOT guarantee all left hand side assignables are included!
		if (lvExp.isLValue()) {
			IASTNode lvAsg = lvExp;
			while (true) {
				lvAsg = ASTUtil.getAncestorOfAsUnless(lvAsg, ASTUtil.AST_ASSIGNMENT_TYPES,
						new Class[] {IASTStatement.class}, true);
				if (lvAsg == null) break;

				if (lvAsg instanceof IASTEqualsInitializer 
						|| isAssignment((IASTInitializerClause) lvAsg)) return true;
//				if (isAssignedTo(lvAsg instanceof IASTEqualsInitializer 
//						? ((IASTEqualsInitializer) lvAsg).getInitializerClause() 
//						: (IASTInitializerClause) lvAsg, 
//						lvExp)) return true;
			}
		}
		return isPassedByRef(lvExp);
	}
	
	
	
	public static boolean isUnaryAssignment(IASTNode initializerOrClause) {
		return (initializerOrClause instanceof IASTUnaryExpression) 
				? isAssignment((IASTUnaryExpression) initializerOrClause) : false;
	}

//	public static boolean isUnaryAssigning(IASTName var) {
//		return isUnaryAssigned(var);
//	}

	public static boolean isBinaryAssignment(IASTNode initializerOrClause) {
		return isPlainBinaryAssignment(initializerOrClause) 
				|| isAbbreviatedBinaryAssignment(initializerOrClause);
	}

	/**
	 * @param init
	 * @param asgn
	 * @return true if {@code asgn} is assigned in {@code init}.
	 */
	public static boolean isBinaryAssignedTo(
			IASTEqualsInitializer init, IASTExpression asgn) {
		if (asgn == null) DebugElement.throwNullArgumentException("assignable");
		return isDirectlyAssignedOf(asgn, init);
	}
	
	/**
	 * @param clause
	 * @param lValue
	 * @return true if {@code lValue} is assigned in {@code clause}.
	 * 	Excluding non-assigned arguments of some assigned arrays, such as the <code>clause</code> array[<code>lValue</code>] = ...
	 */
	public static boolean isBinaryAssignedTo(
			IASTInitializerClause clause, IASTExpression lValue) {
		if (lValue == null) DebugElement.throwNullArgumentException("l-value");
		if (!isBinaryAssignment(clause)) return false;
		
		final IASTExpression lhsAsm = ((IASTBinaryExpression) clause).getOperand1();
		final IASTNode lvArray = ASTUtil.getAncestorOfAs(lValue, ASTUtil.AST_ARRAY_SUB_TYPE, true);
		
		// the <code>clause</code> array[<code>lValue</code>] = ...
		if (lvArray != null 
				&& ASTUtil.hasAncestorAs(lvArray, lhsAsm, null) 
				&& ASTUtil.hasAncestorAs(lValue, ((IASTArraySubscriptExpression) lvArray).getArgument(), null)) 
			return false;
		
		return ASTUtil.hasAncestorAs(lValue, lhsAsm, null);
	}
	
//	public static boolean isBinaryAssigningOf(IASTInitializerClause clause, IASTName var) {
//		return clause == getNonIdExpressionOf(var) 
//				&& isBinaryAssigning(var);
//	}
	
	public static boolean isBinaryAssigning(IASTIdExpression id) {
		return isBinaryAssigningIn(id, null);
	}
	
	public static boolean isBinaryAssigning(IASTName name) {
		return isBinaryAssigning(getIdExpressionOf(name));
	}

	public static boolean isBinaryAssigningIn(IASTExpression exp, IASTInitializerClause clause) {
		IASTNode expParent = exp;
//		final boolean isnLv = !exp.isLValue();
		while (expParent != null) {
			expParent = expParent.getParent();
			if (isAbbreviatedBinaryAssignment(expParent) 
					|| (isPlainBinaryAssignment(expParent) && !isLValueOf(exp, (IASTBinaryExpression) expParent))) 
				if (clause == null || clause == expParent) return true;
		}
		return false;
	}

	public static boolean isPlainBinaryAssignment(IASTNode initializerOrClause) {
		return (initializerOrClause instanceof IASTBinaryExpression 
				&& ((IASTBinaryExpression) initializerOrClause).getOperator() == IASTBinaryExpression.op_assign)
				|| initializerOrClause instanceof IASTEqualsInitializer;
	}

	public static boolean isAbbreviatedBinaryAssignment(IASTNode initializerOrClause) {
		if (initializerOrClause instanceof IASTBinaryExpression)
			switch (((IASTBinaryExpression) initializerOrClause).getOperator()) {
			case IASTBinaryExpression.op_binaryAndAssign	: return true;
			case IASTBinaryExpression.op_binaryOrAssign		: return true;
			case IASTBinaryExpression.op_binaryXorAssign	: return true;
			case IASTBinaryExpression.op_divideAssign		: return true;
			case IASTBinaryExpression.op_minusAssign		: return true;
			case IASTBinaryExpression.op_moduloAssign		: return true;
			case IASTBinaryExpression.op_multiplyAssign		: return true;
			case IASTBinaryExpression.op_plusAssign			: return true;
			case IASTBinaryExpression.op_shiftLeftAssign	: return true;
			case IASTBinaryExpression.op_shiftRightAssign	: return true;
			}
		
		return false;
	}
	
	public static boolean isConstantAssignment(IASTBinaryExpression exp) {
		return isPlainBinaryAssignment(exp) && ASTUtil.isConstant(exp.getOperand2());
	}

	public static boolean isLValueOf(IASTExpression exp, IASTBinaryExpression binary) {
		if (binary == null) DebugElement.throwNullArgumentException("binary");
		return binary.getOperand1().contains(exp);
	}
	
	public static boolean isRewritingAssignment(IASTExpression exp) {
		// every unary and abbreviated binary assignment is rewriting to its (lhs) operand
		if (isUnaryAssignment(exp) || isAbbreviatedBinaryAssignment(exp)) return true;
		
		// lhs of a binary assignment not appearing in rhs is not rewriting to lhs
		if (isPlainBinaryAssignment(exp)) {
			IASTBinaryExpression asg = (IASTBinaryExpression) exp;
			return isRewritingAssignmentTo(asg, getVariableNameOf(asg.getOperand1()));
		}
		
		return false;	// neither unary nor binary assignments
	}

	/**<pre>
	 * Abbreviated binary assignment: var in lhs <-> rewriting (var in rhs but not in lhs <-> not rewriting);
	 * Plain binary assignment: var in both lhs and rhs <-> rewriting.
	 * 
	 * If the given var appears in the rhs of a binary (both plain and abbreviated) assignment BUT NOT in its lhs,
	 * then the var is NOT rewriting.
	 * <br>
	 * 
	 * @param exp - expression filtered as a binary assignment 
	 * @param var - may be in lhs, rhs or neither one of them
	 * @return
	 */
	public static boolean isRewritingAssignmentTo(IASTBinaryExpression exp, IASTName var) {
		if (exp == null || var == null) return false;
		
		// every unary is rewriting to its only operand
//	if (isUnaryAssignment(exp)) 
//		return ((IASTIdExpression) ((IASTUnaryExpression) exp).getOperand()).getName() == var;
		
		// var in lhs <-> rewriting
		if (isAbbreviatedBinaryAssignment(exp)) return ((IASTExpression) var.getParent()).isLValue();
		
		// var in both lhs and rhs <-> rewriting
		if (isPlainBinaryAssignment(exp)) {
			ASTNameCollector varCol = new ASTNameCollector(var.toCharArray());
			IASTName[] lhsVars, rhsVars;
			
			exp.getOperand1().accept(varCol); lhsVars = varCol.getNames();
			exp.getOperand2().accept(varCol); rhsVars = varCol.getNames();
			if (lhsVars != null && rhsVars != null) 	// var in both lhs and rhs
				for (IASTName v : lhsVars) if (((IASTExpression) v.getParent()).isLValue()) return true;
		}
		
		return false;
	}
	
	/**
	 * Every lhs var in a rewriting assignment is rewritingly assigned.
	 * ONLY rhs var's in a binary rewriting one are NOT assigned in one rewriting assignment.
	 * 
	 * @param var
	 * @return
	 */
	public static boolean isRewritinglyAssigned(IASTName var) {
		final IASTExpression varAsg = (IASTExpression) var.getParent().getParent();	// bypassing IASTIdExpression 
		return isUnaryAssignment(varAsg)
				|| ((varAsg instanceof IASTBinaryExpression) 
						&& isRewritingAssignmentTo((IASTBinaryExpression) varAsg, var));
	}

	

	public static boolean isIdExpressionWithNameOf(IASTNode exp, IASTName name) {
		if (exp == null || name == null) return false;
		
		return exp instanceof IASTIdExpression && ((IASTIdExpression) exp).getName().equals(name);
	}
	
	
	
	/**<pre>
	 * A (sub-) array reference is still some memory address (for possibly writing) and different from 
	 * array content for reading only, which means that the reference expression (var ID) must start from 
	 * the left-most IASTArraySubscriptExpression or pointer expression and never be in the subscript arguments.
	 * 
	 * A sub-array reference is in the form of var[...]... (not just ID var), which means 
	 * the reference has fewer levels of subscripts than the array's declared dimension.
	 * <br>
	 * 
	 * @param arrayId
	 * @param clause - the initializer clause or expression that refers the array at some (reference) address
	 * @return
	 */
	public static boolean isArrayReferenceIn(IASTExpression lValue, IASTInitializerClause clause) {
//		TODO: if (clause instanceof IASTInitializerList)...
//		TODO: if (clause instanceof IASTDesignatedInitializer)...
//		TODO: if (clause instanceof ICPPASTInitializerList)...
//		TODO: if (clause instanceof ICPPASTInitializerClause)...

		if (clause instanceof IASTExpression) {
			// the reference has fewer levels of subscripts than the array's declared dimension.
			if (((IASTExpression) clause).getExpressionType() instanceof IArrayType) {
				
				// the reference expression (var ID) must start from the left-most IASTArraySubscriptExpression 
				// or pointer expression and never be in the subscript arguments.
				IASTNode lvOp = lValue;
				while (lvOp != clause) {
					if (lvOp == null) return false;	// arrayId may be null
					lvOp = lvOp.getParent();
				}
				return true;
			}
		}
		
		return false;
//		return getContinuousAncestorCount(arrayOp, IASTArraySubscriptExpression.class) < getDeclaredDim(arrayId);
	}



	/**
	 * Checking if the given variable is accessed (as a top level ID or reference) 
	 * via a function argument. 
	 * TODO (in a separated method): or indirectly accessed via a non-function pointer. 
	 * 
	 * @param lValue
	 * @return
	 */
	public static boolean isPassedByRef(IASTExpression lValue) {
		// TODO: or indirectly used by a non-function pointer...
		IASTInitializerClause varArg = getArgumentExpressionOf(lValue);
		
		if (varArg != null) {
			// var (ID) must be at the top level of parameter (ID)
			// (sub-) array reference (var[...]... or just ID var), not array content 
			if (isArrayReferenceIn(lValue, varArg)) return true;
			// &, 
			if (varArg instanceof IASTUnaryExpression 
					&& ((IASTUnaryExpression) varArg).getOperator() == IASTUnaryExpression.op_amper) 
				return true;
		}
		
		return false;
	}
	
}
