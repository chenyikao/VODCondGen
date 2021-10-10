package ompca.vodcg.condition;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;

/**
 * Like {@link ExpressionRange}, the operands of {@link And} may be merged.
 * 
 * @author Kao. Chen-yi
 *
 */
abstract public class Iff extends And {

	final private Set<Proposition> iffOperands = new HashSet<>();
	private boolean iffInitiates = false;
	
	@Deprecated
	private Iff(Proposition prop1, Proposition prop2) {
		super(new HashSet<>());	// TODO? new HashSet<>({prop1, prop2})
		iffOperands.add(prop1);
		iff(()-> prop2);
	}

	
	
	/**
	 * A <-> A = A -> A = T
	 * 
	 * A <-> B
	 * = (A -> B) /\ (B -> A)
	 * = (~A \/ B) /\ (~B \/ A)
	 * = ~(A /\ ~B) /\ ~(B /\ ~A)
	 * = ~((A /\ ~B) \/ (B /\ ~A))
	 * 
	 * A <-> ~A
	 * = (A -> ~A) /\ (~A -> A)
	 * = (~A \/ ~A) /\ (A \/ A)
	 * = ~A /\ A
	 * = F
	 * 
	 * @param p1
	 * @param p2
	 * @return
	 */
	final public static Proposition from(Proposition p1, Supplier<Proposition> p2) {
		return from(Operator.Iff, p1, p2, () -> {
			return p1.imply(p2).and(()-> p2.get().imply(()-> p1));
		});
	}
	
//	/**
//	 * TODO: 
//	 * A <-> A = A -> A = T
//	 * 
//	 * A <-> ~A 
//	 * = (A -> ~A) /\ (~A -> A)
//	 * 
//	 * @param p1
//	 * @param p2
//	 * @return
//	 */
//	static public Proposition get(Set<Proposition> ps) {
//		if (ps == null || ps.isEmpty()) return null;
//		
//		return new Iff(p1, p2);
//	}
	
	
	
	/**
	 * For separated and precise Proposition/Predicate sub-type and handling.
	 * 
	 * TODO:(A <=> B) /\ C
	 * = (A => B) /\ (B => A) /\ C
	 * = (~A \/ B) /\ (~B \/ A) /\ C
	 * = (~A \/ B) /\ ((~B /\ C) \/ (A /\ C))
	 * = ((~A \/ B) /\ ~B /\ C) \/ ((~A \/ B) /\ A /\ C)
	 * = (((~A /\ ~B) \/ (B /\ ~B)) /\ C) \/ (((~A /\ A) \/ (B /\ A)) /\ C)
	 * = ((~A /\ ~B) /\ C) \/ ((B /\ A) /\ C)
	 * = (~A /\ ~B /\ C) \/ (B /\ A /\ C)
	 * 
	 * @param p2
	 * @return
	 */
	@SuppressWarnings("unchecked")
	protected Proposition andByReduce(Proposition p2) {
		if (dependsOn(p2, null) != null) 
			return this;
		else if (iffInitiates) 
			return super.andByReduce(p2);
		else 
			return And.from((List<Proposition>) toList()).and(()-> p2);
	}
	
	
	
	/**
	 * For separated and precise Proposition/Predicate sub-type and handling.
	 * 
	 * TODO:(A <=> B) \/ C
	 * = ((A => B) /\ (B => A)) \/ C
	 * = ((~A \/ B) /\ (~B \/ A)) \/ C
	 * = (~A \/ B \/ C) /\ (~B \/ A \/ C)
	 * 
	 * @param p2
	 * @return
	 */
	@SuppressWarnings("unchecked")
	protected Proposition orByReduce(Proposition p2) {
		return And.from((List<Proposition>) toList()).or(()-> p2);
	}
	
	
	
	/**
	 * For separated and precise Proposition/Predicate sub-type and handling.
	 * 
	 * (A <=> B) => C
	 * = ~((A => B) /\ (B => A)) \/ C
	 * = ~((~A \/ B) /\ (~B \/ A)) \/ C
	 * = ~(~A \/ B) \/ ~(~B \/ A) \/ C
	 * = (A /\ ~B) \/ (B /\ ~A) \/ C
	 * 
	 * @param p2
	 * @return
	 */
	@SuppressWarnings("unchecked")
	protected Proposition implyByReduce(Proposition p2) {
		return And.from((List<Proposition>) toList()).imply(()-> p2);
	}
	
	
	
	/**
	 * For separated and precise Proposition/Predicate sub-type and handling.
	 * 
	 * @param p2
	 * @return
	 */
	protected Proposition iffByReduce(Proposition p2) {
		if (!iffOperands.contains(p2)) {
//			synchronized (this) {
//				Iterable<Proposition> props = getPropositions();
				iffInitiates = true;
//				if (props == null || 
//						(!props.iterator().hasNext() && iffOperands.size() == 1)) {
//					Proposition firstIff = iffOperands.iterator().next();
//				} else 
				for (Proposition iff : iffOperands) {
					// constructing new Imply's to avoid overriding the Iff operands
					and(()-> ((Proposition) iff.clone()).imply(()-> p2));
					and(()-> p2.imply(()-> iff));
				}
				iffInitiates = false;
//			}
			
			iffOperands.add(p2);
		}
		return this;
	}



//	public boolean hasOnlyOperand() {
//		return iffOperands.size() == 1;
//	}
	
	
	
	/**
	 * @param usesParenthesesAlready indicating enclosing the string by parentheses already or not.
	 * @return
	 */
	protected String toNonEmptyString(boolean usesParenthesesAlready) {
		String str = "";
		for (Proposition iff : iffOperands) 
			str += (((str == "") ? "" : " <=> ") + iff.toNonEmptyString(usesParenthesesAlready));
		return str;
	}
	
}
