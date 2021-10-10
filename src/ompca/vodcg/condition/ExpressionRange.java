/**
 * 
 */
package ompca.vodcg.condition;

import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.Elemental;
import ompca.TrioKeyMap;
import ompca.vodcg.ASTAddressable;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.data.Int;
import ompca.vodcg.condition.data.NumericExpression;
import ompca.vodcg.condition.data.PlatformType;
import ompca.vodcg.condition.version.ArrayAccessVersion;

/**<pre>
 * VariableRange	::= Expression '<=' Variable '<=' Expression
 * 			TODO? 	::= Expression ('<'|'<=') Variable ('<'|'<=') Expression
 * 
 * A convenient class for the <em>inclusive</em> bounds of range.
 * 
 * For various domain scopes a variable range can be in {@link Variable}, {@link Version<Variable>}
 * or {@link VariablePlaceholder} domain.
 * 
 * TODO: arithmetics with other kinds of Expression's.
 * </pre>
 * @author Kao, Chen-yi
 *
 */
public class ExpressionRange<Domain extends Expression> extends OrderRelation
implements NumericExpression {
	
	private static final 
	TrioKeyMap<Expression, ArithmeticExpression, ArithmeticExpression, ExpressionRange<?>> 
	RANGE_CACHE = new TrioKeyMap<>();
	
//	private Collection<OrderRelation> boundRels;
//	private OrderRelation lowerBoundRel = null;
//	private OrderRelation upperBoundRel = null;

	// 'null' means unknown, different from infinity
	private ArithmeticExpression	lowerBound = null;
	private Domain					domain = null;
	private ArithmeticExpression	upperBound = null;

//	/**
//	 * TODO? adjusting bounds for non {@link OrderRelation.Operator#LessEqual} op.
//	 * 
//	 * @param lb
//	 * @param lbOp
//	 * @param var
//	 * @param ubOp
//	 * @param ub
//	 */
//	@SuppressWarnings("unchecked")
//	private VariableRange(Expression lb, OrderRelation.Operator lbOp, 
//			VariableVersionDelegate var, OrderRelation.Operator ubOp, 
//			Expression ub) {
//	}
	
	/**
	 * @param lb
	 * @param dom
	 * @param ub
	 */
	private ExpressionRange(ArithmeticExpression lb, Domain dom, ArithmeticExpression ub) {
//		this(	lb, 
//				OrderRelation.Operator.LessEqual, 
//				var, 
//				OrderRelation.Operator.LessEqual, 
//				ub);
		super(OrderRelation.Operator.LessEqual, (Expression) lb, dom, (Expression) ub);
		
		assert dom != null;
		domain = dom;
		lowerBound = lb;
		upperBound = ub;
		setFinal();
//		boundRels = (Collection<OrderRelation>) operands;
//		upperBoundRel = new OrderRelation(OrderRelation.Operator.LessEqual, var, upperBound = ub);
//		and(upperBoundRel);
//		lowerBoundRel = boundRels.iterator().next();
//		if (lbOp == ubOp) upperBoundRel = lowerBoundRel;
	}
	
	/**
	 * @param domVar
	 * @param lb
	 * @param ub
	 * @return
	 */
	@SuppressWarnings("deprecation")
	public static <Domain extends Expression> Proposition from(Domain domVar, 
			ArithmeticExpression lb, ArithmeticExpression ub) {
		if (domVar == null) throwNullArgumentException("domain");
		
		if (lb == null || ub == null) try {
			final PlatformType dt = (PlatformType) domVar.getType();
			if (lb == null) lb = Elemental.getNonNull(()-> dt.getNegativeInfinity());
			if (ub == null) ub = Elemental.getNonNull(()-> dt.getPositiveInfinity());

			if (!(lb instanceof Expression) || !(ub instanceof Expression)) 
				returnTodoException("unsupported ranges");
			if (tests(ub.isLessThan(lb))) 
				throwInvalidityException("upperBound < lowerBound");
			if (tests(lb.equals(ub))) 
				return Equality.from(domVar, (Expression) lb);	// upperBound = lowerBound
			
		} catch (ClassCastException e) {
			throwTodoException(e);
		} catch (Exception e) {
			throwUnhandledException(e);
		}
		@SuppressWarnings("unchecked")
		ExpressionRange<Domain> vr = (ExpressionRange<Domain>) RANGE_CACHE.get(domVar, lb, ub);
		if (vr == null) RANGE_CACHE.put(
					domVar, 
					lb, 
					ub, 
					vr = new ExpressionRange<>(lb, domVar, ub));
		return vr;
	}
	
	public static Proposition fromIteratorAfter(
			IASTStatement loop, final ASTAddressable rtAddr, VODCondGen condGen) {
		if (loop instanceof IASTForStatement) return fromIteratorOf(
				(IASTForStatement) loop, false, true, rtAddr, condGen);
//		if (loop instanceof IASTWhileStatement)
//			return computeIndexOf((IASTWhileStatement) loop, asn, cg);
		return throwTodoException("unsupported loop");
	}
	
	public static Proposition fromIteratorBefore(
			IASTForStatement loop, final ASTAddressable rtAddr, VODCondGen condGen) {
		return fromIteratorOf(loop, true, false, rtAddr, condGen);
	}
	
	/**
	 * @param loop
	 * @param condGen
	 * @return
	 */
	public static Proposition fromIteratorOf(
			final IASTStatement loop, final ASTAddressable rtAddr, final VODCondGen condGen) {
		if (loop instanceof IASTForStatement) return fromIteratorOf(
				(IASTForStatement) loop, false, false, rtAddr, condGen);
//		if (loop instanceof IASTWhileStatement)
//			return computeIndexOf((IASTWhileStatement) loop, asn, cg);
		return throwTodoException("unsupported loop");
	}
	
	/**
	 * @param loop
	 * @param isBefore
	 * @param isAfter
	 * @param condGen
	 * @return
	 */
	private static Proposition fromIteratorOf(IASTForStatement loop, 
			boolean isBefore, boolean isAfter, final ASTAddressable rtAddr, VODCondGen condGen) {
		assert !(isBefore && isAfter);	// isBefore xor isAfter
		
		try {
		final PathVariablePlaceholder it = 
				PathVariablePlaceholder.fromCanonicalIteratorOf(loop, rtAddr, condGen);
		final ArithmeticExpression lb = ArithmeticExpression.fromLowerBoundOf(loop, rtAddr, condGen), 
				ub = ArithmeticExpression.fromUpperBoundOf(loop, rtAddr, condGen);
		
		if (isBefore) return from(it, null, lb);
		if (isAfter) return from(it, ub, null);
		return from(it, lb, ub);
		
		} catch (Exception e) {
//		} catch (UncertainPlaceholderException | ASTException | IncomparableException | NoSuchVersionException e) {
			return throwTodoException(e);
		}
	}
	
	

	public static ArithmeticExpression throwDomainException() {
		throwTodoException("unsupported domain");
		return null;
	}


	
//	public ConditionElement getScope() {
//		ConditionElement scope = super.getScope();
//		// lazy scope setting
//		// TODO: lb.scope \/ {var.scope} \/ ub.scope
//		if (scope == null && variable != null) 
//			setScope(scope = variable.iterator().next().getScope());
//		return scope;
//	}
	
	/**
	 * TODO: support multiple domains(variables).
	 * @return
	 */
	public Domain getDomain() {return domain;}
	
	@Override
	public Expression getLowerBound() {return (Expression) lowerBound;}
	@Override
	public Expression getUpperBound() {return (Expression) upperBound;}

//	public Proposition getBoundsRelation() {
//		if (lowerBoundRel == null) return upperBoundRel;
//		if (upperBoundRel == null) return lowerBoundRel;
//		return lowerBoundRel.and(upperBoundRel);
//	}
	


	@Override
	protected Boolean cacheConstant() {
		if (lowerBound == null || upperBound == null) return null;	// may be called during super-class construction
		return testsSkipNull(()-> lowerBound.isConstant() && upperBound.isConstant());
	}
	
//	@Override
//	public boolean isPositiveInfinity() {
//		assert lowerBound != null && upperBound != null;
//		// TODO? checking oo/-oo contradiction
//		return Elemental.testsAnySkipNullException(
//				()-> lowerBound.isPositiveInfinity(),
//				()-> upperBound.isPositiveInfinity());
//	}
//
//	@Override
//	public boolean isNegativeInfinity() {
//		assert lowerBound != null && upperBound != null;
//		// TODO? checking oo/-oo contradiction
//		return Elemental.testsAnySkipNullException(
//				()-> lowerBound.isNegativeInfinity(),
//				()-> upperBound.isNegativeInfinity());
//	}
	

	
	/**
	 * lb1 <= v <= ub1  /\  	lb2 <= 	v <= ub2,
	 * 						or	lb2 <= 	v 		,	=
	 * 						or			v <= ub2  
	 * (non-overlapping) 	if	ub1 < lb2 - 1 or ub2 < lb1 - 1:	new And
	 * (overlapping) 		if	lb1 < lb2 < ub1 < ub2: 			lb1 <= v <= ub2
	 * 							lb2 < lb1 < ub2 < ub1:			lb2 <= v <= ub1
	 * 							lb1 < ub1 < ub2: 				lb1 <= v <= ub2
	 * 							lb1 < ub2 < ub1:				lb1*<= v <= ub1
	 * 							lb1 < lb2 < ub1: 				lb1 <= v <= ub1*
	 * 							lb2 < lb1 < ub1:				lb2 <= v <= ub1
	 * (containing) 		if	lb1 <= lb2 <= ub2 <= ub1:		lb1 <= v <= ub1
	 * 							lb2 <= lb1 <= ub1 <= ub2:		lb2 <= v <= ub2
	 * 							lb1 <= ub2 <= ub1:				lb1 <= v <= ub1
	 * 							lb1 <= ub1 <= ub2:				lb1*<= v <= ub2
	 * 							lb1 <= lb2 <= ub1:				lb1 <= v <= ub1
	 * 							lb2 <= lb1 <= ub1:				lb2 <= v <= ub1*
	 * 
	 * @see ompca.vodcg.condition.And#andReduced(ompca.vodcg.condition.Proposition)
	 */
	@SuppressWarnings("unchecked")
	protected Proposition andByReduce(Proposition p2) {
		if (p2 == null) throwNullArgumentException("p2");
		
		Relation.Operator op2 = p2.getOp();
		assert getOp() != null && op2 != null;
			
		boolean isP2Er = p2 instanceof ExpressionRange && domain == ((ExpressionRange<?>) p2).domain,
				isP2Or = p2 instanceof OrderRelation && getOp() == op2;
		final ExpressionRange<Domain> vr2 = isP2Er ? (ExpressionRange<Domain>) p2 : null;
		final OrderRelation or2 = isP2Or ? (OrderRelation) p2 : null;
		
		if (!(isP2Er && equalsVariable(vr2)) &&
				!(isP2Or && equalsVariable(or2))) return super.andByReduce(p2);
					
		final ArithmeticExpression lb2 = isP2Er ? (ArithmeticExpression) vr2.lowerBound 
				: (isP2Or ? getSkipException(()-> (ArithmeticExpression) or2.getLowerBound()) : null), 
			ub2 = isP2Er ? (ArithmeticExpression) vr2.upperBound 
					: (isP2Or ? getSkipException(()-> (ArithmeticExpression) or2.getUpperBound()) : null);
		if (lb2 != null && ub2 != null) {
			// (non-overlapping) 	if	ub1 < lb2 - 1 or ub2 < lb1 - 1:	new And
			if (Elemental.tests(()-> 
			upperBound.isLessThan(lb2.subtract(Int.ONE)) || ub2.isLessThan(lowerBound.subtract(Int.ONE)))) 
				return super.andByReduce(p2);
			
			// (overlapping) 		if	lb1 < lb2 < ub1 < ub2: 		lb1 <= v <= ub2
			// 							lb1 < ub1 < ub2: 			lb1 <= v <= ub2
			// (containing) 		if	lb1 <= ub1 <= ub2:			lb1*<= v <= ub2
			if (Elemental.tests(()-> 
			(lowerBound.isLessThan(lb2) && lb2.isLessThan(upperBound) && upperBound.isLessThan(ub2))
					|| (lowerBound.isLessThan(lowerBound) && upperBound.isLessThan(ub2))
					|| (lowerBound.isLessEqual(upperBound) && upperBound.isLessEqual(ub2))))
				return ExpressionRange.from(domain, lowerBound, ub2);
			
			
			// (overlapping) 		if	lb2 < lb1 < ub2 < ub1:		lb2 <= v <= ub1
			// 							lb2 < lb1 < ub1:			lb2 <= v <= ub1
			// (containing) 		if	lb2 <= lb1 <= ub1:			lb2 <= v <= ub1*
			if (Elemental.tests(()-> 
			(lb2.isLessThan(lowerBound) && lowerBound.isLessThan(ub2) && ub2.isLessThan(upperBound))
					|| (lb2.isLessThan(lowerBound) && lowerBound.isLessThan(upperBound))
					|| (lb2.isLessEqual(lowerBound) && lowerBound.isLessEqual(upperBound))))
				return ExpressionRange.from(domain, lb2, upperBound);

			// 							lb1 < ub2 < ub1:			lb1*<= v <= ub1
			// 							lb1 < lb2 < ub1: 			lb1 <= v <= ub1*
			if (Elemental.tests(()-> (lowerBound.isLessThan(ub2) && ub2.isLessThan(upperBound))
					|| (lowerBound.isLessThan(lb2) && lb2.isLessThan(upperBound))))
				return ExpressionRange.from(domain, lowerBound, upperBound);
			
			// (containing) 		if	lb1 <= lb2 <= ub2 <= ub1:	lb1 <= v <= ub1
			// 							lb1 <= ub2 <= ub1:			lb1 <= v <= ub1
			// 							lb1 <= lb2 <= ub1:			lb1 <= v <= ub1
			if (Elemental.tests(()-> 
			(lowerBound.isLessEqual(lb2) && lb2.isLessEqual(ub2) && ub2.isLessEqual(upperBound)) ||
				(lowerBound.isLessEqual(ub2) && ub2.isLessEqual(upperBound)) ||
				(lowerBound.isLessEqual(lb2) && lb2.isLessEqual(upperBound))))
				return this;
			
			// 							lb2 <= lb1 <= ub1 <= ub2:	lb2 <= v <= ub2
			if (Elemental.tests(()-> 
			lb2.isLessEqual(lowerBound) && lowerBound.isLessThan(upperBound) && upperBound.isLessThan(ub2))) 
				return p2;
		}
		
		return super.andByReduce(p2);
	}

	protected Proposition implyByReduce(Proposition p2) {
		return p2 instanceof ExpressionRange 
				? implyByReduce((ExpressionRange<?>) p2)
				: null;
	}
	
	private Proposition implyByReduce(ExpressionRange<?> r2) {
		assert r2 != null;
		
		final Expression d2 = r2.getDomain();
		if (d2 != domain) return null;
		
		final ArithmeticExpression lb2 = r2.lowerBound, ub2 = r2.upperBound;
		if (Elemental.tests(()-> lb2.isLessEqual(lowerBound) && upperBound.isLessEqual(ub2))) 
			return True.from("(lb2 <= lb <= x <= ub <= ub2 -> lb2 <= x <= ub2) = T", Proposition.Operator.Imply, this, r2);
//		if (tests(()-> !lowerBound.isLessThan(lb2) || !upperBound.isLessThan(ub2))) return 
//				r2.or(domain.less(lowerBound)).or(upperBound.less(domain));
		return null;
	}
	
	
	/**
	 * @param er2
	 * @return
	 */
	public boolean equalsVariable(ExpressionRange<Domain> er2) {
		assert domain != null;
		if (er2 == null) return false;
		
		final Domain d2 = er2.domain;
		if (d2 == null) return false;
		
		Boolean result = domain.equals(d2);
		// elemental non-equal means variable non-equal 
		return result == null ? false : result;	
	}

	/**
	 * @param or
	 * @return
	 */
	public boolean equalsVariable(OrderRelation or) {
		assert domain != null;
		if (or == null) return false;
		
		for (Expression e : or.getOperands()) 
			if (e instanceof PathVariablePlaceholder 
					&& domain.equals(e)) return true;
		return false;
	}
	

	
	/**
	 * This method becomes immutable if the lower bound equals upper one 
	 * and then is merged to an {@link Equality}.
	 */
	@Override
	protected Expression reduceOnce() {
		return lowerBound != null && upperBound != null && Elemental.tests(lowerBound.equals(upperBound)) ? 
				Equality.from(domain, (Expression) lowerBound) : super.reduceOnce();
	}
	
	@Override
	protected Expression toConstantIf() {
		return this;
	}

	/**
	 * @see ompca.vodcg.condition.Relation#toNonEmptyString(boolean)
	 */
	@Override
	protected String toNonEmptyString(boolean usesParenAlready) {
		final String opStr = OrderRelation.Operator.LessEqual.toString();
		return ((usesParenAlready) ? "" : "(") 
				+ ((Expression) lowerBound).toNonEmptyString(false)	+ " "
				+ opStr 											+ " "
				+ domain.toString() 								+ " "
				+ opStr						 						+ " "
				+ ((Expression) upperBound).toNonEmptyString(false) 
				+ (usesParenAlready ? "" : ")");
	}

	@Override
	public String toZ3SmtString(boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs) {
		final String sup = super.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition, isLhs);

		// for constant or non-array-accessing domain
		if (sup.isBlank() || !(domain instanceof ArrayAccessVersion)) return sup;
		
		return "(forall (" 
		+ ((ArrayAccessVersion<?>) domain).toZ3SmtLocalParamsDeclaration(true) 
		+ ") " + sup + ")";
	}

}