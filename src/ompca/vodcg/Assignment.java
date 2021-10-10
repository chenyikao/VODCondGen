/**
 * 
 */
package ompca.vodcg;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTInitializerList;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import ompca.Elemental;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.Equality;
import ompca.vodcg.condition.Expression;
import ompca.vodcg.condition.Function;
import ompca.vodcg.condition.FunctionCall;
import ompca.vodcg.condition.PathVariablePlaceholder;
import ompca.vodcg.condition.Proposition;
import ompca.vodcg.condition.VariablePlaceholder;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class Assignment extends SystemElement {

	// union structure: assert !(asgIc != null && asgEi != null);
	private IASTInitializerClause asmIc = null;
	private IASTEqualsInitializer asmEi = null;
	private Proposition asmEq = null;
	
	final private Set<Assignable<?>> asds = new HashSet<>();
	final private Set<Assignable<?>> asns = new HashSet<>();
	
	private Assignment(IASTInitializerClause clause, final ASTAddressable dynaAddr, VODCondGen condGen) {
		super(dynaAddr, condGen);
		asmIc = clause;
	}

	private Assignment(IASTEqualsInitializer init, final ASTAddressable dynaAddr, VODCondGen condGen) {
		super(dynaAddr, condGen);
		asmEi = init;
	}



	static public Assignment from(IASTForStatement loop, final ASTAddressable dynaAddr, VODCondGen condGen) {
		if (loop == null) throwNullArgumentException("loop");
		return new Assignment(ASTLoopUtil.getCanonicalInitializerOf(loop), dynaAddr, condGen);
	}
	
	static public Assignment from(IASTEqualsInitializer init, final ASTAddressable dynaAddr, VODCondGen condGen) {
		if (init == null) throwNullArgumentException("initializer");
		return new Assignment(init, dynaAddr, condGen);
	}
	
	/**
	 * @param clause
	 * @param assigned - possibly a function call argument
	 * @param condGen
	 * @return
	 */
	static public Assignment from(
			final IASTInitializerClause clause, final Assignable<?> assigned, final VODCondGen condGen) 
			throws UncertainPlaceholderException {
		if (clause == null) throwNullArgumentException("clause");
		if (assigned == null) throwNullArgumentException("assigned");

		final ASTAddressable dynaAddr = assigned.cacheRuntimeAddress();
		final IASTExpression asdExp = assigned.getExpressionView();
		if (ASTAssignableComputer.isAssignedIn(asdExp, clause)
				|| ASTAssignableComputer.isAssigningIn(asdExp, clause)) 
			return new Assignment(clause, dynaAddr, condGen);
		
		if (ASTAssignableComputer.isLikeAssignment(clause)) 
			return from(ASTUtil.getEnclosingFunctionCallOf(clause), assigned, condGen);
		
		return null;
	}

	/**
	 * @param call
	 * @param arg
	 * @param condGen
	 * @return
	 */
	static public Assignment from(
			final IASTFunctionCallExpression call, final Assignable<?> arg, final VODCondGen condGen) 
			throws UncertainPlaceholderException {
		if (call == null) throwNullArgumentException("function call expression");
		if (arg == null) throwNullArgumentException("function call argument");

		// TODO: may accept assigned library functions if arguments have assignment side-effect
		if (Function.from(call, arg.cacheRuntimeAddress(), condGen).isInLibrary()) return null;
		
		// traversing function call for arg's assigned-ness
		final ASTAddressable dynaAddr = arg.cacheRuntimeAddress();
		if (!arg.isArrayArgument())	try { 
			assert arg.isCallArgument();
			final VariablePlaceholder<?> param = 
					arg.getEnclosingCallParameter();
//					arg.getEnclosingCall().getParameter(arg);
			if (param instanceof PathVariablePlaceholder) {
				for (Assignable<?> p : Assignable.fromOf(
						((PathVariablePlaceholder) param).getAssignable()
						.getWritingFunctionDefinition(), 
						param.getName(), arg.cacheRuntimeAddress(), condGen)) 
					if (tests(p.isAssigned())) return p.getFirstAssignment();	//new Assignment(call, condGen);
			} else	
				// non-AST parameter causing function call assignment
				if (param.isAssigned()) return new Assignment(call, dynaAddr, condGen);
					
		} catch (ASTException e) {	
			// for ambiguous function definitions, etc.
			return new Assignment(call, dynaAddr, condGen);
		} catch (UncertainPlaceholderException e) {
			throw e;
		} catch (Exception e) {
			throwUnhandledException(e);
		}
		return null;
	}
	
	
	
//	private void init() {
//		getAssigned().setAssignment(this);
//		getAssigners().setAssignment(this);
//	}
	

	
	public Assignable<?> getAssigned() throws ASTException {
		try {collectAssignables();}
		catch (UncertainException e) {
			if (!e.excludesAssigneds()) throwUnhandledException(e);
		}
		
		if (asds.size() == 1) {
			final Assignable<?> asd = asds.iterator().next();
			assert asd != null && tests(asd.isAssigned());
			return asd;
		}
		else if (asds.isEmpty()) 
			return throwTodoException("unsupported assignment");
		return throwTodoException("multiple assigneds");
	}
	
	public Set<Assignable<?>> getAssigneds() throws ASTException {
		collectAssignables();
		return asds;
	}
	
	public List<Expression> getAssigners() throws ASTException {
		final List<Expression> les = new ArrayList<>();
		final IASTInitializerClause ic = getAssignerClause();
		final VODCondGen cg = getCondGen();
		final ASTAddressable da = cacheRuntimeAddress();
		
		if (ic instanceof IASTInitializerList) 
			for (IASTInitializerClause lic : ((IASTInitializerList) ic).getClauses()) 
				les.add(Expression.fromRecursively(lic, da, cg));
		
		else les.add(Expression.fromRecursively(ic, da, cg));
//		try {
//			les.add(((Equality) toEquality()).getAssigner());
//		} catch (ClassCastException e) {
//			throwTodoException(e);
//		}
		
		return les;
	}
	
	public IASTInitializerClause getAssignerClause() {
		assert !(asmIc != null && asmEi != null);
		
		if (asmEi != null) return asmEi.getInitializerClause();
		
		if (asmIc instanceof IASTUnaryExpression) 
			return ((IASTUnaryExpression) asmIc).getOperand();

		if (ASTAssignableComputer.isAbbreviatedBinaryAssignment(asmIc)) 
			return asmIc;
		if (ASTAssignableComputer.isPlainBinaryAssignment(asmIc)) 
			return ((IASTBinaryExpression) asmIc).getOperand2();
		
		return throwTodoException(asmIc != null
				? ASTUtil.toStringOf(asmIc) : "assignment without assigners");
	}

	/**
	 * @return non-null set of assigner assignable's.
	 */
	public Set<Assignable<?>> getAssignerAssignables() 
			throws ASTException, UncertainException {
		try {collectAssignables();}
		catch (UncertainException e) {
			if (!e.excludesAssigners()) throw e;
		}
		// UncertainException e => e.excludesAssigners() 
		//	=> assigners are certain
		
		return asns;
//		final Set<Assignable> asners = new HashSet<>();
//		for (Assignable asn : asns) 
//			if (!asn.isArrayArgument()) asners.add(asn);
//		return asners;
	}
	
	public FunctionCall<?> getCallAssigner() throws ASTException {
		return asmIc instanceof IASTFunctionCallExpression
				? FunctionCall.fromRecursively(
						(IASTFunctionCallExpression) asmIc, (Supplier<Proposition>) null, cacheRuntimeAddress(), getCondGen())
				: null;
	}

//	/**
//	 * @return null <em>only if</em> this assignment is not initialized
//	 * 	explicitly.
//	 * @throws ASTException
//	 */
//	public Expression getDirectAssigner() throws ASTException {
//		return applySkipNull(ac->
//		Expression.fromRecursively(ac, getCondGen()),
//		()-> getAssignerClause());
//	}

	
	
	public Function getFunctionScope() {
		final ASTAddressable rtAddr = cacheRuntimeAddress();
		if (asmEi != null) return Function.getFunctionScopeOf(asmEi, rtAddr, getCondGen());
		if (asmIc != null) return Function.getFunctionScopeOf(asmIc, rtAddr, getCondGen());
		return null;
	}

	
	
	/**
	 * asn-- || --asn || asn -= const || asn += -const
	 * @return
	 */
	public boolean assignsDecreasingly() {
		final Expression ae = getAssigned().getAssigner();
		if (!(ae instanceof ArithmeticExpression)) throwTodoException("unsupported assignment");
		final ArithmeticExpression aae = (ArithmeticExpression) ae;
		if (asmIc != null) {
			if (asmIc instanceof IASTUnaryExpression) 
				switch (((IASTUnaryExpression) asmIc).getOperator()) {
				case IASTUnaryExpression.op_postFixDecr	: return true;
				case IASTUnaryExpression.op_prefixDecr	: return true;
				}
			else if (asmIc instanceof IASTBinaryExpression) 
				switch (((IASTBinaryExpression) asmIc).getOperator()) {
				case IASTBinaryExpression.op_divideAssign : 
				case IASTBinaryExpression.op_minusAssign : 	return Elemental.tests(aae.isPositive());
				case IASTBinaryExpression.op_plusAssign	: 	return Elemental.tests(aae.isNegative());
				}
		}
		return false;
	}

	/**
	 * asn++ || ++asn || asn += const || asn -= -const
	 * @return
	 */
	public boolean assignsIncreasingly() {
		final Expression ae = getAssigned().getAssigner();
		if (!(ae instanceof ArithmeticExpression)) throwTodoException("unsupported assignment");
		final ArithmeticExpression aae = (ArithmeticExpression) ae;
		if (asmIc != null) {
			if (asmIc instanceof IASTUnaryExpression) 
				switch (((IASTUnaryExpression) asmIc).getOperator()) {
				case IASTUnaryExpression.op_postFixIncr	: return true;
				case IASTUnaryExpression.op_prefixIncr	: return true;
				}
			else if (asmIc instanceof IASTBinaryExpression) 
				switch (((IASTBinaryExpression) asmIc).getOperator()) {
				case IASTBinaryExpression.op_multiplyAssign	: 
				case IASTBinaryExpression.op_minusAssign	: 	return Elemental.tests(aae.isNegative());
				case IASTBinaryExpression.op_plusAssign		: 	return Elemental.tests(aae.isPositive());
				}
		}
		return false;
	}
	
	private void collectAssignables() 
			throws ASTException, UncertainException {
		assert !(asmIc != null && asmEi != null);
		final VODCondGen cg = getCondGen();
		
		if (asmEi != null) {
			asds.add(Assignable.from(((IASTDeclarator) asmEi.getParent()).getName(), null, cg));
			asns.addAll(Assignable.fromOf(asmEi.getInitializerClause(), null, cg));
		}
		
		else if (isUnary()) {
			final Assignable<?> asnd = Assignable.from(
					((IASTUnaryExpression) asmIc).getOperand(), null, cg);
			asns.add(asnd);
			asds.add(asnd);
		}
		
		else if (isBinary()) {
			asds.add(Assignable.from(
					((IASTBinaryExpression) asmIc).getOperand1(), null, cg));
			for (IASTName rhsName : ASTUtil.getDescendantsOfAs(
					getAssignerClause(), IASTName.class)) try {
				final Assignable<?> rhs = Assignable.from(rhsName, null, cg);
				/* rhsLv == this && asgm is binary 
				 * => lv's not at lhs && lv's not unary-assigned
				 */
				if (rhs != null) asns.add(rhs);
			} catch (ASTException e) {
				throw new UncertainException(e, this).excludeAssigneds();
			}
		}
		
		// non-AST function call assignment
		else if (asmIc instanceof IASTFunctionCallExpression) {
			final IASTInitializerClause[] args = 
					((IASTFunctionCallExpression) asmIc).getArguments();
			if (args != null) for (IASTInitializerClause arg : args) {
				final Assignable<?> argAsn = Assignable.from(arg, null, cg);
				if (argAsn == null) continue;
				if (tests(argAsn.isAssigned())) asds.add(argAsn);
				else asns.add(argAsn);
			}
		}
		
		else if (asmIc != null) throwTodoException(
				"unsupported assignment " + ASTUtil.toStringOf(asmIc));
	}
	

	
	public boolean contains(IASTNode node) {
		return (asmIc != null && asmIc.contains(node))
				|| (asmEi != null && asmEi.contains(node));
	}
	
	@Override
	protected Boolean cacheConstant() {
		return getAssigned().isConstant();
	}
	
	protected boolean equalsToCache(SystemElement se2) throws ClassCastException, NullPointerException {
		final Assignment asm2 = (Assignment) se2;
		return (asmIc != null && asmIc.equals(asm2.asmIc))
				|| (asmEi != null && asmEi.equals(asm2.asmEi));
	}
	
	public boolean selfAssigns() {
		if (isAbbreviatedBinary()) return true;
		
		for (Assignable<?> asd : getAssigneds())
			for (Assignable<?> asnr : getAssignerAssignables())
				if (asnr.equals(asd)) return true;
		return false;
	}
	
	public boolean isUnary() {
		return asmIc instanceof IASTUnaryExpression
				? ASTAssignableComputer.isAssignment((IASTUnaryExpression) asmIc) 
				: false;
	}
	
	public boolean isBinary() {
		return isPlainBinary() || isAbbreviatedBinary();
	}
	
	public boolean isPlainBinary() {
		return (asmIc instanceof IASTBinaryExpression 
				&& ((IASTBinaryExpression) asmIc).getOperator() == 
				IASTBinaryExpression.op_assign)
				|| asmEi != null;
	}

	public boolean isAbbreviatedBinary() {
		return ASTAssignableComputer.isAbbreviatedBinaryAssignment(asmIc);
	}
	
	/**
	 * A direct assignment is said <em>assigned by</em> rhs and <em>assigned to</em> lhs.
	 * While a call-by-reference assignment is an indirect one.
	 * 
	 * @return
	 */
	public boolean isDirect() {
		return isUnary() || isBinary();
	}
	
	public boolean isDirectlyAssignedTo(IASTName lhs) {
		return isDirect() 
				&& (asmEi != null
				? ASTAssignableComputer.isDirectlyAssignedOf(lhs, asmEi)
				: ASTAssignableComputer.isDirectlyAssignedOf(lhs, asmIc));
	}
	

	
	public boolean isFunctionCall() {
		return asmIc instanceof IASTFunctionCallExpression;
	}
	
	/**
	 * @return
	 */
	public IASTNode toASTNode() {
		assert !(asmIc != null && asmEi != null);
		if (asmEi != null) return asmEi;
		if (asmIc != null) return asmIc;
		return null;
	}

	@SuppressWarnings("unchecked")
	@Override
	protected Assignment toConstantIf() {
		return this;
	}
	
//	public IASTInitializerClause toClause() {
//		assert !(asmIc != null && asmEi != null);
//		return asmEi != null
//				? asmEi.getInitializerClause()
//				: asmIc;
//	}
	
	/**
	 * @return single equality or conjunction of equalities if this is an array assignment
	 * @throws ASTException
	 */
	public Proposition toEquality() throws ASTException {
		if (asmEq != null) return asmEq;
		
		try {
			assert !(asmIc != null && asmEi != null);
			final VODCondGen cg = getCondGen();
			return asmEq = asmEi != null
					? Equality.from(asmEi, cacheRuntimeAddress(), cg)
					: Proposition.fromRecursivelyWithoutBranching(asmIc, this, cg);
			
		} catch (ClassCastException e) {
			return throwTodoException(e);
		}
	}
	
	@Override
	public String toString() {
		assert !(asmIc != null && asmEi != null);
		if (asmEi != null) return ASTUtil.toStringOf(asmEi);
		if (asmIc != null) return ASTUtil.toStringOf(asmIc);
		return null;
	}

}