/**
 */
package ompca.vodcg.condition;

import java.util.Collection;
import java.util.Collections;
import java.util.EnumMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

import ompca.Elemental;
import ompca.Mappable;
import ompca.MultiPartitionMap;
import ompca.vodcg.VODCondGen;

/**
 * Predicate	::= Quantification? Proposition		// default Quantification to 'exists'
 * 
 * A proposition is default to an exists predicate.
 * 
 * @author Kao, Chen-yi
 *
 */
public class Predicate extends Proposition {

	public enum Operator implements Relation.Operator {
		Exists, Forall;
		
		@Override
		public Boolean isUnary() {return true;}

		@Override
		public <M extends Map<?,?>> EnumMap<? extends Key, M> createPartitionMap() {
			return new EnumMap<>(Operator.class);
		}
		
		@Override
		public <M extends Mappable<?, ?>> EnumMap<? extends Key, M> createPartitionMappable() {
			return new EnumMap<>(Operator.class);
		}

		/* (non-Javadoc)
		 * @see ompca.condition.Relation.Operator#negate()
		 */
		@Override
		public ompca.vodcg.condition.Relation.Operator negate() {
			switch (this) {
			case Exists:			return Forall;
			case Forall:			return Exists;
			default:
				assert(false); return null;	// should NOT come here!
			}
		}
		
		
		
		public <H extends Relation> String toZ3SmtString(
				H host, boolean printsVariableDeclaration, boolean printsFunctionDefinition) {
			switch (this) {
			case Exists:			return "";
			case Forall:			return "forall";
			default:
				assert(false); return null;	// should NOT come here!
			}
		}

	}

	
	
	final static private MultiPartitionMap<Proposition, Predicate> 
	EXISTS_CACHE = new MultiPartitionMap<>();
	final static private MultiPartitionMap<Proposition, Predicate> 
	FORALL_CACHE = new MultiPartitionMap<>();
	final static private Map<Operator, MultiPartitionMap<Proposition, Predicate>> 
	OPERATION_CACHE = new EnumMap<>(Operator.class);

	final protected Set<VariablePlaceholder<?>> quantifiers = new HashSet<>();
	
	

	protected Predicate(
			Operator op, Set<VariablePlaceholder<?>> quantifiers, Proposition prop) {
		super(op, Collections.singletonList(prop), prop.getScopeManager());
//		TODO: locals = prop.locals;
		
		this.quantifiers.addAll(quantifiers);
		prop.setScope(()-> this);
		prop.checkDependency(this);
	}

	/**
	 * A copy constructor from Proposition to Predicate.
	 * 
	 * @param quantifier
	 * @param prop
	 * @param scopeManager 
	 */
	protected Predicate(VariablePlaceholder<?> quantifier, Proposition prop, 
			VODCondGen scopeManager) {
		super(Operator.Exists, Collections.singletonList(prop), scopeManager);
		assert prop != null; 
//		TODO: locals = prop.locals;
		
//		if (quantifier == null) 
//			throw new IllegalArgumentException("Must provide a quantifier!");

		quantifiers.add(quantifier);
		prop.setScope(()-> this);
		prop.checkDependency(this);
	}

	/**
	 * Convenient factory method for reducing and caching reusable range implications.
	 * 
	 * @param op
	 * @param expRanges
	 * @param prop
	 * @param constructor
	 * @return 
	 */
	protected static Proposition from(
			Operator op, List<ExpressionRange<? extends Expression>> expRanges, Proposition prop, 
			java.util.function.Function<Set<VariablePlaceholder<?>>, Predicate> constructor) {
//	protected static Proposition from(
//			Operator op, List<ExpressionRange<VariablePlaceholder<?>>> varRanges, Proposition prop, 
//			java.util.function.Function<Set<VariablePlaceholder<?>>, Predicate> constructor) {
		if (expRanges == null) throwNullArgumentException("variable ranges");
		if (prop == null) throwNullArgumentException("proposition");
		
		if (Elemental.tests(prop.isConstant())) return prop;
		
//		List<ExpressionRange<Version<Variable>>> rvrs = new ArrayList<>();
//		Proposition eqs = null;
//		for (ExpressionRange<Version<Variable>> vr : varRanges) {
//			Expression rvr = vr.reduceOnce();
//			if (rvr != vr) {
//				if (rvr instanceof Equality) {
//					Equality eq = (Equality) rvr;
//					eqs = eqs == null ? eq : eqs.and(()-> eq);
//				} 
//				else returnTodoException("unsupported reduction");
//			} else if (prop.dependsOn(vr.getDomain())) rvrs.add(vr);
//		}
//		// an equality (singleton) range mean a dequantified exist-predicate
//		if (eqs != null) return from(op, rvrs, eqs.imply(()-> prop), constructor);
		
		Set<VariablePlaceholder<?>> qs = new HashSet<>();
		for (ExpressionRange<? extends Expression> vr : expRanges)
			qs.addAll((Collection<? extends VariablePlaceholder<?>>) 
					vr.getDomain().getDirectVariablePlaceholders());

		return from(op, qs, And.from(expRanges).imply(()-> prop), ()-> constructor.apply(qs));
	}

	/**
	 * Factory method for reducing and caching reusable predicates.
	 * 
	 * @param op
	 * @param quantifiers
	 * @param prop
	 * @param constructor
	 * @return
	 */
	protected static Proposition from(Operator op, 
			Set<VariablePlaceholder<?>> quantifiers, Proposition prop, Supplier<Predicate> constructor) {
		if (op == null) throwNullArgumentException("operator"); 
//		if (quantifiers == null || quantifiers.isEmpty()) throwNullArgumentException("quantifiers");
		if (prop == null) throwNullArgumentException("proposition");
		
		if (Elemental.tests(prop.isConstant()) || !prop.dependsOn(quantifiers)) return prop;
		
//		p1 = (Proposition) p1.reduce(); 
//		p2 = (Proposition) p2.reduce();
		
		if (OPERATION_CACHE.isEmpty()) {
			OPERATION_CACHE.put(Operator.Exists, EXISTS_CACHE);
			OPERATION_CACHE.put(Operator.Forall, FORALL_CACHE);
		}
		MultiPartitionMap<Proposition, Predicate> opCache = OPERATION_CACHE.get(op);
		Predicate result = opCache.get(prop);
		
		if (result == null) result = constructor.get();
		
//		opCache.put(ps, result);	// caching the most reduced result at last
		opCache.put(prop, result);
		return result;
//		return result.clone();
	}



	/**
	 * Ex: SE = (P1 && P1.SE) || (P2 && P2.SE) || ... || (Pn && Pn.SE) = P.SE
	 * Fx: SE = (P1 && P1.SE) && (P2 && P2.SE) && ... && (Pn && Pn.SE) = TODO
	 */
	protected <OT extends Expression> boolean cacheOperandDirectSideEffect(final OT oprd) 
			throws ClassCastException {
		return cacheExpressionalOperandDirectSideEffect(oprd);
	}
	
	public Set<VariablePlaceholder<?>> getQuantifiers() {
		return Collections.unmodifiableSet(quantifiers);
	}
	
	public Proposition getProposition() {
		return (Proposition) getFirstOperand();
	}
	

	
	protected Proposition andByReduce(Proposition p2) {
		if (p2 == null) throwNullArgumentException("p2");
		return reduceByOp(Proposition.Operator.And, p2);
	}
	
//	private Proposition andByReduce(Predicate pred) {
//		assert pred != null;
//		
//		Set<Version<Variable>> nqs = new HashSet<>(quantifiers); 
//		nqs.addAll(pred.getQuantifiers());
//		return new Predicate((Operator) getOp(), nqs,
//				((Proposition) getFirstOperand()).and((Proposition) pred.getFirstOperand()));
//	}

	protected Proposition orByReduce(Proposition p2) {
		if (p2 == null) throwNullArgumentException("p2");
		return reduceByOp(Proposition.Operator.Or, p2);
	}
	
	protected Proposition implyByReduce(Proposition p2) {
		if (p2 == null) throwNullArgumentException("p2");
		return reduceByOp(Proposition.Operator.Imply, p2);
	}
	
	protected Proposition iffByReduce(Proposition p2) {
		if (p2 == null) throwNullArgumentException("p2");
		return reduceByOp(Proposition.Operator.Iff, p2);
	}
	
	
	
	/**<pre>
	 * Guard method for any pre-/post-processing:
	 * 
	 * Fx(B /\ (C -> ((D /\ Fx(...)) /\ E)))
	 * = Fx(B /\ (~C \/ (D /\ E /\ Fx(...))))
	 * = Fx(B) /\ Fx(~C \/ (D /\ E /\ Fx(...)))
	 * = Fx(B) /\ ~Ex~(~C \/ (D /\ E /\ Fx(...)))
	 * = Fx(B) /\ ~Ex(C /\ ~(D /\ E /\ Fx(...)))
	 * = Fx(B) /\ ~(C /\ ~(D /\ E /\ Fx(...)))
	 * = Fx(B) /\ (~C \/ (D /\ E /\ Fx(...)))
	 * = (Fx(B) /\ ~C) \/ (Fx(B) /\ D /\ E /\ Fx(...))
	 * = (Fx(B) /\ ~C) \/ (D /\ E /\ Fx(B /\ ...))
	 * = (Fx(B) /\ ~C) \/ (D /\ E /\ Fx(...))
	 * = ??(Fx(B) /\ ~C) \/ (D /\ E /\ Fx(...))
	 * = ??(Fx(B) /\ ~C) \/ (~Fx~(D /\ E) /\ Fx(...))
	 * = ??Fx((B /\ ~C) \/ (B /\ D /\ E /\ Fx(...)))
	 * 
	 * @see ompca.condition.Proposition#notByReduce()
	 */
	protected Proposition notByReduce() {
		Proposition p = (Proposition) getFirstOperand();
		if (p == null) throwNullArgumentException("operand");
		
//		p.checkDependency(this);

		Proposition np = p.not();
		switch ((Operator) getOp()) {
		case Exists:	return Forall.from(quantifiers, np); 
		case Forall:	return np;
		default:		return null;
		}
	}
	
	/**
	 * This method becomes immutable if the proposition is constant 
	 * and then de-quantified from the predicate.
	 */
	@Override
	protected Expression reduceOnce() {
		final Proposition prop = getProposition();
		return Elemental.tests(prop.isConstant()) ? prop : super.reduceOnce();
	}

	/**
	 * @param op
	 * @param p2
	 * @return
	 */
	private Proposition reduceByOp(Proposition.Operator op, Proposition p2) {
		assert op != null && p2 != null;
		
		Proposition prop = getProposition(), propNew = null;
		Relation.Operator op1 = getOp();
		assert op1 instanceof Operator;
		if (op1.equals(p2.getOp())) {
			Predicate pred2 = (Predicate) p2;
			if (quantifiers.equals(pred2.getQuantifiers())) {
				Supplier<Proposition> prop2 = ()-> pred2.getProposition();
				switch (op) {
				// Ex(A) /\ Ex(B) = Ex(A /\ B), Fx(A) /\ Fx(B) = Fx(A /\ B)
				case And:	propNew = prop.and(prop2);		break;
				case Or:	propNew = prop.or(prop2);		break;
				case Imply:	propNew = prop.imply(prop2);	break;
				case Iff:	propNew = prop.iff(prop2);		break;
				default:	returnTodoException("Predicate " + op + " p2?");
				}
				if (propNew != prop) return op1.equals(Operator.Forall) 
						? Forall.from(quantifiers, propNew)
						: new Predicate((Operator) op1, quantifiers, propNew);
				else return this;
			}
		}
		
//		if (Variable.conflictsByName(quantifiers, p2.getVariableReferences())) {
//		}
		
//		checkDependency(op, p2);
//		p2.checkDependency(op, this);	// for and/or/iff -> setOnlyOperand(...)
		
		// merging newProp to this predicate regardless quantifiers
		switch (op) {
		case And:	return super.andByReduce(p2);
		case Or:	return super.orByReduce(p2);
		case Imply:	return super.implyByReduce(p2);
		case Iff:	return super.iffByReduce(p2);
		default:	returnTodoException("Predicate " + op + " p2");
		}
		return null;
	}
	

	
//	@Override
//	public String toZ3SmtString(boolean printsVariableDeclaration, boolean printsFunctionDefinition) {
//		return super.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition);	// default Quantification to 'exists'
//	}

}