/**
 * 
 */
package ompca.vodcg;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.NavigableSet;
import java.util.Set;
import java.util.TreeSet;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarationStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpressionStatement;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTInitializer;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import ompca.DebugElement;
import ompca.Elemental;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.ExpressionRange;
import ompca.vodcg.condition.data.Int;
import ompca.vodcg.parallel.OmpDirective;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public final class ASTLoopUtil {

	static final Set<IASTForStatement> NON_CANONICAL_LOOP_CACHE = new HashSet<>();

	//	private static final Map<IASTForStatement, IASTDeclarator>	LOOP_INITIAL_DECL_CACHE 		= new HashMap<>();

	private static final Map<IASTForStatement, IASTInitializerClause> 
	LOOP_INITIAL_BOUND_CACHE 	= new HashMap<>();
	private static final Map<IASTForStatement, IASTExpression> 	
	LOOP_TEST_BOUND_CACHE 		= new HashMap<>();
	private static final Map<IASTForStatement, Integer> 		
	LOOP_TEST_OP_TO_VAR_CACHE 	= new HashMap<>();

	private static final Map<IASTForStatement, ArithmeticExpression[]> 	
	LOOP_BOUND_CACHE 		= new HashMap<>();
	private static final Map<IASTForStatement, Int> 			
	LOOP_INCREMENT_CACHE	= new HashMap<>();
	
	// TODO: caching all reusable utility method results

	
	
	public static boolean isConstant(IASTForStatement loop, final ASTAddressable dynaAddr, VODCondGen condGen) {
		if (loop == null) return false;
		if (isInitializedConstantly(loop) && isConditionedConstantly(loop) && iteratesConstantly(loop)) return true;
		return Elemental.tests(ExpressionRange.fromIteratorOf(loop, dynaAddr, condGen).isConstant());
	}
	


	public static ArithmeticExpression[] getBoundsOf(IASTStatement loop) {
		if (loop instanceof IASTForStatement) return getBoundsOf((IASTForStatement) loop);
		return DebugElement.throwTodoException("unsupported loop");
	}
	
	public static ArithmeticExpression[] getBoundsOf(IASTForStatement loop) {
		return LOOP_BOUND_CACHE.get(loop);
	}

	public static ArithmeticExpression getLowerBoundOf(IASTStatement loop) {
		return getBoundsOf(loop)[0];
	}
	
	public static ArithmeticExpression getUpperBoundOf(IASTStatement loop) {
		return getBoundsOf(loop)[1];
	}
	
	
	
	public static IASTInitializerClause getCanonicalInitialBoundOf(IASTForStatement loop) {
		if (isNonCanonical(loop)) return null;
		
		IASTInitializerClause ib = LOOP_INITIAL_BOUND_CACHE.get(loop);
		if (ib != null) return ib;
		
		ib = getCanonicalInitializerOf(loop);
//		if (ASTLValueComputer.isUnaryAssignment(ib)) Debug.throwTodoException("unsupported bound?");
		if (ASTAssignableComputer.isBinaryAssignment(ib)) ib = ((IASTBinaryExpression) ib).getOperand2();
		else DebugElement.throwTodoException("unsupported bound");

		if (ib != null) LOOP_INITIAL_BOUND_CACHE.put(loop, ib);
		return ib;
	}
	
	/**<pre>
	 *	for (init-expr; test-expr; incr-expr) structured-block
	 * 		init-expr 	One of the following:
	 * 					var = lb
	 * 					integer-type var = lb
	 * 					random-access-iterator-type var = lb
	 * 					pointer-type var = lb
	 * 
	 *		var 		One of the following:
	 *						A variable of a signed or unsigned integer type.
	 *						TODO: For C++, a variable of a random access iterator type.
	 *						TODO: For C, a variable of a pointer type.
	 *					If this variable would otherwise be shared, it is implicitly made private in the
	 *					loop construct. This variable must not be modified during the execution of the
	 *					for-loop other than in incr-expr. Unless the variable is specified lastprivate
	 *					or linear on the loop construct, its value after the loop is unspecified.
	 * 
	 *		lb and b 	Loop invariant expressions of a type compatible with the type of var.
	 * <br>
	 * 
	 * @param loop
	 * @return
	 */
	public static IASTInitializerClause getCanonicalInitializerOf(IASTForStatement loop) {
		if (isNonCanonical(loop)) return null;
		
		IASTInitializerClause iz = null;
		final IASTStatement is = loop.getInitializerStatement();
		if (is instanceof IASTDeclarationStatement) {
//				IASTDeclarator idr = LOOP_INITIAL_DECL_CACHE.get(loop);
//				if (idr == null) {
//					LOOP_INITIAL_DECL_CACHE.put(declStat, idr = ((IASTSimpleDeclaration) idn).getDeclarators()[0]);
//				}
			final IASTDeclaration idn = ((IASTDeclarationStatement) is).getDeclaration();
			if (idn instanceof IASTSimpleDeclaration) {
				final IASTName itn = ASTUtil.getNameOf(getCanonicalIteratorOf(loop));
				for (IASTDeclarator id : ((IASTSimpleDeclaration) idn).getDeclarators()) 
					if (ASTUtil.equals(itn, id.getName(), true)) {
						final IASTInitializer i = id.getInitializer();
						if (i instanceof IASTEqualsInitializer) 
							iz = ((IASTEqualsInitializer) i).getInitializerClause();
					}
			}
			
		} else if (is instanceof IASTExpressionStatement) {
			iz = ((IASTExpressionStatement) is).getExpression();
			
		} // TODO: else if ...
		
		if (iz == null) setNonCanonical(loop);
		return iz;
	}

	public static IASTExpression getCanonicalIteratorOf(IASTForStatement loop) {
		IASTExpression lie = loop.getIterationExpression();
		if (lie instanceof IASTUnaryExpression) lie = ((IASTUnaryExpression) lie).getOperand();
		
		// binary incr-expr
		else if (lie instanceof IASTBinaryExpression) {
			final IASTBinaryExpression bie = (IASTBinaryExpression) lie;
			switch (bie.getOperator()) {
			// 					var += incr
			case IASTBinaryExpression.op_plusAssign:
				// 					var -= incr
			case IASTBinaryExpression.op_minusAssign: 
				// 					var = var + incr
				//					var = incr + var
				// 					var = var - incr
			case IASTBinaryExpression.op_assign: lie = bie.getOperand1(); break;
			default: // TODO
			}
		}
		return lie;
	}
	
	/**	<pre>
	 * 		test-expr	One of the following:
	 * 					var relational-op b
	 * 					b relational-op var
	 * 
	 *		var 		One of the following:
	 *						A variable of a signed or unsigned integer type.
	 *						TODO: For C++, a variable of a random access iterator type.
	 *						TODO: For C, a variable of a pointer type.
	 *					If this variable would otherwise be shared, it is implicitly made private in the
	 *					loop construct. This variable must not be modified during the execution of the
	 *					for-loop other than in incr-expr. Unless the variable is specified lastprivate
	 *					or linear on the loop construct, its value after the loop is unspecified.
	 *
	 *		relational-op 	One of the following:
	 * 						<
	 * 						<=
	 * 						>
	 * 						>=
	 * 
	 *		lb and b 	Loop invariant expressions of a type compatible with the type of var.
	 * <br>
	 * 
	 * @param loop
	 * @param condGen 
	 * @return
	 */
	public static IASTExpression getCanonicalTestBoundOf(
			IASTForStatement loop, VODCondGen condGen) {
		return (IASTExpression) getCanonicalTestOpToVarOrBoundOf(loop, true, condGen);
	}
	
	public static int getCanonicalTestOperatorToVarOf(
			IASTForStatement loop, VODCondGen condGen) {
		Object op = getCanonicalTestOpToVarOrBoundOf(loop, false, condGen);
		if (op instanceof Integer) return (int) op;
		DebugElement.throwTodoException("Non-canonical loop?");
		return -1;
	}
	
	private static Object getCanonicalTestOpToVarOrBoundOf(
			IASTForStatement loop, boolean wantsBound, VODCondGen condGen) {
		if (isNonCanonical(loop)) return null;

		IASTExpression tb = LOOP_TEST_BOUND_CACHE.get(loop);
		Integer top = LOOP_TEST_OP_TO_VAR_CACHE.get(loop);
		if (tb == null || top == null) {
			final IASTExpression condExp = loop.getConditionExpression();
			if (condExp instanceof IASTBinaryExpression) {
				final IASTBinaryExpression condBin = (IASTBinaryExpression) condExp;
				final int op = condBin.getOperator();
				final IASTExpression oprd1 = condBin.getOperand1(), oprd2 = condBin.getOperand2(), 
						it = getCanonicalIteratorOf(loop);
				if (ASTAssignableComputer.getDependentOnBy(oprd1, it) != null) {	// var relational-op b
					tb = oprd2; switch (op) {
					case IASTBinaryExpression.op_lessThan: top = IASTBinaryExpression.op_greaterThan; break;
					case IASTBinaryExpression.op_lessEqual: top = IASTBinaryExpression.op_greaterEqual; break;
					case IASTBinaryExpression.op_greaterThan: top = IASTBinaryExpression.op_lessThan; break;
					case IASTBinaryExpression.op_greaterEqual: top = IASTBinaryExpression.op_lessEqual; break;
					}
				}
				else if (ASTAssignableComputer.getDependentOnBy(oprd2, it) != null) {	// b relational-op var
					tb = oprd1; top = op;
				}
				// tb keeps null if loop is not canonical 
			}

			if (tb == null || top == null) setNonCanonical(loop);
			else {
				LOOP_TEST_BOUND_CACHE.put(loop, tb);
				LOOP_TEST_OP_TO_VAR_CACHE.put(loop, top);
			}
		}
		return wantsBound ? tb : top;
	}

	/**<pre>
	 * ({@linkplain OpenMP 嚜瞥ttp://www.openmp.org/mp-documents/openmp-4.5.pdf})
	 * 
	 * 嚜�2.6 Canonical Loop Form
	 * 	A loop has canonical loop form if it conforms to the following:
	 * 
	 * 		for (init-expr; test-expr; incr-expr) structured-block
	 * 			init-expr 	One of the following:
	 * 						var = lb
	 * 						integer-type var = lb
	 * 						random-access-iterator-type var = lb
	 * 						pointer-type var = lb
	 * 
	 * 			test-expr 	One of the following:
	 * 						var relational-op b
	 * 						b relational-op var
	 * 
	 * 			incr-expr 	One of the following:
	 * 						++var
	 * 						var++
	 * 						--var
	 * 						var--
	 * 						var += incr
	 * 						var -= incr
	 * 						var = var + incr
	 * 						var = incr + var
	 * 						var = var - incr
	 * 
	 * 			var 		One of the following:
	 * 							A variable of a signed or unsigned integer type.
	 * 							TODO: For C++, a variable of a random access iterator type.
	 * 							TODO: For C, a variable of a pointer type.
	 * 						If this variable would otherwise be shared, it is implicitly made private in the
	 * 						loop construct. This variable must not be modified during the execution of the
	 * 						for-loop other than in incr-expr. Unless the variable is specified lastprivate
	 * 						or linear on the loop construct, its value after the loop is unspecified.
	 * 
	 * 			relational-op 	One of the following:
	 * 							<
	 * 							<=
	 * 							>
	 * 							>=
	 * 
	 * 			lb and b 	Loop invariant expressions of a type compatible with the type of var.
	 * 
	 * 			incr 		A loop invariant integer expression.
	 * 
	 * 	The canonical form allows the iteration count of all associated loops to be computed before
	 * 	executing the outermost loop. The computation is performed for each loop in an integer type. This
	 * 	type is derived from the type of var as follows:
	 * 
	 * 		�� 	If var is of an integer type, then the type is the type of var.
	 * 		�� 	TODO: For C++, if var is of a random access iterator type, then the type is the type that would 
	 * 			be used by std::distance applied to variables of the type of var.
	 * 		�� 	TODO: For C, if var is of a pointer type, then the type is ptrdiff_t.
	 * 
	 * 	The behavior is unspecified if any intermediate result required to compute the iteration count
	 * 	cannot be represented in the type determined above.
	 * 
	 * 	There is no implied synchronization during the evaluation of the lb, b, or incr expressions. It is
	 *  unspecified whether, in what order, or how many times any side effects within the lb, b, or incr
	 *	expressions occur.
	 *
	 *	Note �� Random access iterators are required to support random access to elements in constant
	 *	time. Other iterators are precluded by the restrictions since they can take linear time or offer limited
	 *	functionality. It is therefore advisable to use tasks to parallelize those cases.
	 *
	 *	Restrictions
	 *	
	 *	The following restrictions also apply:
	 *	
	 *		�� 	If test-expr is of the form var relational-op b and relational-op is < or <= then incr-expr must
	 *			cause var to increase on each iteration of the loop. If test-expr is of the form 
	 *			'var relational-op b' and relational-op is > or >= then incr-expr must cause var to decrease on 
	 *			each iteration of the loop.
	 *		�� 	If test-expr is of the form 'b relational-op var' and relational-op is < or <= then incr-expr must
	 *			cause var to decrease on each iteration of the loop. If test-expr is of the form 
	 *			'b relational-op var' and relational-op is > or >= then incr-expr must cause var to increase on 
	 *			each iteration of the loop.
	 *		�� 	TODO: For C++, in the simd construct the only random access iterator types that are allowed for 
	 *			var are pointer types.
	 *		�� 	The b, lb and incr expressions may not reference var of any of the associated loops.
	 * <br>
	 *
	 * @param loop
	 * @param sideEffect 
	 * @param condGen 
	 * @return
	 */
	public static boolean isCanonical(IASTForStatement loop, VODCondGen condGen) {
		if (isNonCanonical(loop)) return false;
		if (getCanonicalInitialBoundOf(loop) == null 
				|| getCanonicalTestBoundOf(loop, condGen) == null)
//				|| Int.fromCanonicalIncrementOf(loop, condGen) == null) 
			return false;
		return true;
	}
	
	/**
	 * @param loop
	 * @return
	 */
	public static boolean isNonCanonical(IASTForStatement loop) {
		return loop == null || NON_CANONICAL_LOOP_CACHE.contains(loop);
	}
	
	/**
	 * @param loop
	 */
	public static void setNonCanonical(IASTForStatement loop) {
		NON_CANONICAL_LOOP_CACHE.add(loop);
	}
	
	public static ArithmeticExpression[] setBoundsOf(IASTForStatement loop, ArithmeticExpression[] bounds) {
		return LOOP_BOUND_CACHE.put(loop, bounds);
	}
	


	/**<pre>
	 * Retrieving the direct parent loop within the same function definition.
	 * </pre>
	 * 
	 * @param node
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public static IASTForStatement getEnclosingLoopOf(IASTNode node) {
		return (IASTForStatement) ASTUtil.getAncestorOfAsUnless(
				node, 
				new Class[] {IASTForStatement.class},
				new Class[] {IASTFunctionDefinition.class}, 
				false);
	}
	
	/**<pre>
	 * Retrieving the direct parent loop within the same function definition.
	 * 
	 * Only supporting the OpenMP canonical for-loop 
	 * ({@linkplain OpenMP http://www.openmp.org/mp-documents/openmp-4.5.pdf}).
	 * 
	 * TODO: getEnclosingLoopCondition(...) for handling break/continue statements and while-loop conditions.
	 * <br>
	 * 
	 * @param innerLoop
	 * @return
	 */
	public static IASTForStatement getEnclosingLoopOf(IASTForStatement innerLoop) {
		return (IASTForStatement) ASTUtil.getAncestorOfAsUnless(
				innerLoop, 
				ASTUtil.AST_FOR_TYPE,
				ASTUtil.AST_FUNCTION_DEFINITION, 
				false);
	}
	
	
	
	public static boolean isLoop(IASTStatement stat) {
		for (Class<IASTStatement> clz : ASTUtil.AST_LOOP_TYPES) 
			if (clz.isInstance(stat)) return true;
		return false;
	}
	
	public static boolean isLoopParallel(IASTStatement loop, VODCondGen condGen) {
		if (!isLoop(loop)) return false;
		
		return Elemental.tests(()-> 
		OmpDirective.fromEnclosing(loop, condGen).getStatement() == loop);
	}
	
	/**<pre>
	 * Constant iteration is stronger than the loop invariant iteration.
	 * 
	 *		lb and b 	Loop invariant expressions of a type compatible with the type of var.
	 *		incr 		A loop invariant integer expression.
	 * <br>
	 *
	 * @param i - the loop iterator
	 * @return
	 */
	public static boolean isLoopIteratorConstant(IASTName i) {
		final IASTExpression exp = (IASTExpression) i.getParent().getParent();	//bypassing IASTIdExpression
		IASTForStatement loop;

		/*	for (init-expr; test-expr; incr-expr) structured-block
		 * 		init-expr 	One of the following:
		 * 					var = lb
		 * 					TODO: integer-type var = lb
		 * 					TODO: random-access-iterator-type var = lb
		 * 					TODO: pointer-type var = lb
		 */ 
		if (ASTAssignableComputer.isPlainBinaryAssignment(exp)) {	// when exp is the assignment part of init-expr
			//bypassing the IASTExpressionStatement initializer statement
			loop = (IASTForStatement) exp.getParent().getParent();	
			return ASTAssignableComputer.isConstantAssignment((IASTBinaryExpression) exp) 
					&& isConditionedConstantly(loop) && iteratesConstantly(loop);
		}

		/* 		test-expr 	One of the following:
		 * 					var relational-op b
		 * 					b relational-op var
		 */
		if (ASTUtil.isBinaryRelation(exp)) {	// exp is test-expr
			loop = (IASTForStatement) exp.getParent();
			return isInitializedConstantly(loop) 
					&& isRelatedConstantly((IASTBinaryExpression) exp) && iteratesConstantly(loop);
		}

		/* 		incr-expr 	One of the following:
		 * 					++var
		 * 					var++
		 * 					--var
		 * 					var--
		 * 					var += incr
		 * 					var -= incr
		 * 					var = var + incr
		 *					var = incr + var
		 * 					var = var - incr
		 * 
		 *		var 		One of the following:
		 *						A variable of a signed or unsigned integer type.
		 *						TODO: For C++, a variable of a random access iterator type.
		 *						TODO: For C, a variable of a pointer type.
		 *					If this variable would otherwise be shared, it is implicitly made private in the
		 *					loop construct. This variable must not be modified during the execution of the
		 *					for-loop other than in incr-expr. Unless the variable is specified lastprivate
		 *					or linear on the loop construct, its value after the loop is unspecified.
		 */ 
		if (ASTAssignableComputer.isRewritingAssignment(exp)) {	// exp is incr-expr, which only concerns linear increments
			loop = (IASTForStatement) exp.getParent();
			return isInitializedConstantly(loop) 
					&& isConditionedConstantly(loop) 
					&& (exp instanceof IASTBinaryExpression)?increasesConstantly((IASTBinaryExpression) exp):true;
		}
		
		return false;
	}



	public static boolean isInitializedConstantly(IASTForStatement loop) {
		//	for (init-expr; test-expr; incr-expr) structured-block
		final IASTStatement init = loop.getInitializerStatement();
		 
		/* 		init-expr 	One of the following:
		 * 					var = lb
		 */
		if (init instanceof IASTExpressionStatement) {
			final IASTExpression initExp = ((IASTExpressionStatement) init).getExpression();
			if (ASTAssignableComputer.isPlainBinaryAssignment(initExp))
				return ASTAssignableComputer.isConstantAssignment((IASTBinaryExpression) initExp);
		}

		/* 					TODO: integer-type var = lb
		 * 					TODO: random-access-iterator-type var = lb
		 * 					TODO: pointer-type var = lb
		 */ 
		return false;
	}
	
	public static boolean isConditionedConstantly(IASTForStatement loop) {
		//	for (init-expr; test-expr; incr-expr) structured-block
		final IASTExpression testExp = loop.getConditionExpression();	// TODO: getCanonicalConditionOf(loop)
		if (ASTUtil.isBinaryRelation(testExp)) 
			return isRelatedConstantly((IASTBinaryExpression) testExp);
		
		return false;
	}
	
	public static boolean isRelatedConstantly(IASTBinaryExpression rel) {
		/* 		test-expr 	One of the following:
		 * 					var relational-op b
		 * 					b relational-op var
		 */
		return rel.getOperand1() instanceof IASTLiteralExpression 
				^ rel.getOperand2() instanceof IASTLiteralExpression;
	}

	

	public static boolean iteratesConstantly(IASTForStatement loop) {
		return increasesConstantly(loop.getIterationExpression());
	}

	public static boolean increasesConstantly(IASTExpression exp) {
		return ASTAssignableComputer.isUnaryAssignment(exp)  
				|| (exp instanceof IASTBinaryExpression && increasesConstantly((IASTBinaryExpression) exp));
	}
	
	public static boolean increasesConstantly(IASTBinaryExpression exp) {
		final IASTExpression incrExp = exp.getOperand2();
		
		/* 					var += incr
		 * 					var -= incr
		 */
		if (ASTAssignableComputer.isAbbreviatedBinaryAssignment(exp)) 
			return ASTUtil.isConstant(incrExp);
		
		/* 					var = var + incr
		 *					var = incr + var
		 * 					var = var - incr
		 */
		else if (ASTAssignableComputer.isPlainBinaryAssignment(exp) && incrExp instanceof IASTBinaryExpression) {
			IASTBinaryExpression incrAdd = (IASTBinaryExpression) incrExp;
			// a constant (IASTLiteralExpression) has no name (IASTName)
			return ASTUtil.isConstant(incrAdd.getOperand1()) || 
					ASTUtil.isConstant(incrAdd.getOperand2());
		}
		
		return false;
	}

	
	
	public static Int getIncrementOf(IASTForStatement loop) {
		return LOOP_INCREMENT_CACHE.get(loop);
	}

	public static Int setIncrementOf(IASTForStatement loop, Int incr) {
		return LOOP_INCREMENT_CACHE.put(loop, incr);
	}



	public static NavigableSet<IASTStatement> toNavigableSet(Collection<IASTStatement> loops, VODCondGen condGen) {
		final NavigableSet<IASTStatement> loopSet = 
				new TreeSet<>(new ASTRuntimeLocationComputer(condGen));
		loopSet.addAll(loops);
		return loopSet;
	}

}