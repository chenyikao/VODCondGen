/**
 * 
 */
package ompca.vodcg.condition;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * @author Kao, Chen-yi
 *
 */
public class Not extends Proposition {

//	final static private Map<Proposition, Proposition> NotCache = new HashMap<>();
//	static private Map<Proposition, Proposition> NotCache = null;

	
	
	public Not(Proposition subject) {
		super(	Operator.Not, 
				Arrays.asList(subject),
				subject.getScopeManager());
	}


	
//	final public static Proposition get(Proposition p) {
//		if (p == null) return null;
//		if (p.getOp() == Operator.Not) return ((Not) p).notByReduce();
//		
//		/* Don't use HashMap since {@link And#equalsToCache()} depends on 
//		 * {@link Proposition#not()} and makes cycle.
//		 */
//		if (NotCache == null) NotCache = new TreeMap<>(p);
//		Proposition np = NotCache.get(p);
//		if (np != null) return np;
//		
//		np = p.notByReduce();
//		if (np == null) np = new Not(p);
//
//		NotCache.put(p, np); 
//		return np;
////		return np.clone();
//	}

	
	
	/**
	 * SE = ~(P && P.SE)
	 */
	@Override
	protected <OT extends Expression> boolean cacheOperandDirectSideEffect(final OT oprd)
			throws ClassCastException {
		final Proposition prop = (Proposition) getFirstOperand();
		andSideEffect(()-> prop.getSideEffect().and(()-> prop).not());
		return false;
	}

	
	
	/**
	 * ~(B /\ (C \/ (D /\ A))) /\ A
	 * = (~B \/ (~C /\ (~D \/ ~A))) /\ A
	 * = (~B \/ (~C /\ ~D) \/ (~C /\ ~A)) /\ A
	 * = (~B /\ A) \/ (~C /\ ~D /\ A) \/ (~C /\ ~A /\ A)
	 * = (~B /\ A) \/ (~C /\ ~D /\ A)
	 * = (~B \/ (~C /\ ~D)) /\ A
	 * = (~B \/ ~(C \/ D)) /\ A
	 * = ~(B /\ (C \/ D)) /\ A
	 * 
	 * @see ompca.condition.Proposition#andByReduce(ompca.condition.Proposition)
	 */
	protected Proposition andByReduce(Proposition p2) {
		if (p2 == null) throwNullArgumentException("p2");
	
		Proposition result = null;
		Relation.Operator op2 = p2.getOp();
		if (op2 == Operator.Or) result = andByReduce((Or) p2);
		if (result != null) return result;
		
		final ReductionOperations ros = new ReductionOperations();
		ros.add(Operator.And, null, null, (not, B)-> And.from(B).not().and(()-> p2));
		ros.add(Operator.Or, null, null, (b, C)-> Or.from(C));
		ros.add("~(B && (C || (D && A))) && A = ~(B && (C || D)) && A",
				Operator.And, (c, d)-> d.equals(p2), null, (c, newD)-> And.from(newD));

		result = not().reduceByOperands(ros, false);
		if (result != null) return result;
		
		return super.andByReduce(p2);
	}
	
	/**
	 * ~A /\ (A \/ B)
	 * = (~A /\ A) \/ (~A /\ B)
	 * = ~A /\ B
	 * 
	 * @param p2
	 * @return
	 */
	private Proposition andByReduce(Or p2) {
		assert p2 != null;
		
		Proposition nA = not(); 
		List<Proposition> B = new ArrayList<>();
		boolean isReduced = false;
		
		for (Proposition b : p2.getPropositions()) {
			// ~A /\ (A \/ B) = ~A /\ B
			if (nA.equals(b)) {isReduced = true; continue;}
			else B.add(b);
		}
		return isReduced ? nA.and(()-> Or.from(B)) : null;
	}

	
	
	protected Proposition orByReduce(Proposition p2) {
		if (p2 == null) throwNullArgumentException("p2");
		
		Proposition result = null;
		Relation.Operator op2 = p2.getOp();
		if (op2 == Operator.Imply) result = orByReduce((Imply) p2);
		if (result != null) return result;
		
		return super.orByReduce(p2);
	}
	
	/**
	 * ~A \/ (A -> B)
	 * = ~A \/ (~A \/ B)
	 * = ~A \/ B
	 * 
	 * @param p2
	 * @return
	 */
	private Proposition orByReduce(Imply p2) {
		// ~A \/ (A -> B) = ~A \/ B
		if (not().equals(p2.antecedent)) return p2;
		return null;
	}

	/**
	 * ~(~A) = A
	 * 
	 * @see ompca.condition.Proposition#notByReduce()
	 */
	protected Proposition notByReduce() {
		// ~(~A) = A
		return (Proposition) getFirstOperand();
	}
	
	
	
//	/**
//	 * Overriding infix serialization.
//	 *  
//	 * @see ompca.condition.ConditionElement#toNonEmptyString(boolean)
//	 */
//	@Override
//	public String toNonEmptyString(boolean usesParenAlready) {
//		assert (subject != null);
//
//		boolean usesParen = false;
//		if (subject instanceof Relation && !((Relation)subject).op.isAssociativeTo(op)) 
//			usesParen = true;
//		return op.toString() 
//				+ ((usesParen)?"(":"") 
//				+ subject.toNonEmptyString(usesParen) 
//				+ ((usesParen)?")":"");
//	}
	
	
	
//	@Override
//	public String toZ3SmtString(boolean printsVariableDeclaration, boolean printsFunctionDefinition) {
//		if (subject == null) return null;
//		else return "(not " + subject.toZ3SmtString(false, false) + ")";
//	}

}