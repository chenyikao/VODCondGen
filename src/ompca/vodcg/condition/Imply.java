/**
 * 
 */
package ompca.vodcg.condition;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.Stack;
import java.util.function.Supplier;

import ompca.Elemental;
import ompca.vodcg.condition.ReductionOperations.ReductionOctet;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class Imply extends Proposition {
	
//	private boolean guardsImply = false;

	protected Proposition antecedent = null;	// implicant
	protected Proposition consequent = null;	// implicand
	
	
	
	/**
	 * Both antecedent and consequent are assumed optimized already.
	 * 
	 * @param antec
	 * @param consq
	 */
	private Imply(Proposition antec, Proposition consq) {
		super(Operator.Imply, Arrays.asList(antec, consq), antec.getScopeManager());
		
		assert antec != null && consq != null;
//		if (!antec.guardsImply() && !consq.guardsImply()) 
//			throw new UnsupportedOperationException("Call Proposition.imply() first!");
//		if (consq == null || consq.isEmpty()) 
//			throw new IllegalArgumentException("Empty consequent is NOT allowed!");
		
		antecedent = antec;
		consequent = consq;
		// NOT a complete Imply yet during construction, so don't call imply(...)!
//		implyReduced(consq);
	}
	
	/**
	 * Antecedent-only construction for better utilizing 
	 * {@link Proposition#imply(Proposition)} after the completion of Imply
	 * construction.
	 * 
	 * @param antec
	 */
	private Imply(Proposition antec) {
		super(Operator.Imply, Arrays.asList(antec), antec.getScopeManager());
		antecedent = antec;
	}
	
//	public Imply(VOPConditions antec, VOPConditions consq) {
//		super(Operator.Imply, new ArrayList<Proposition>(), 
//				antec.getScopeManager());
//
//		And antics = antec.getPathCondition().getAssertions(), 
//				consqs = consq.getPathCondition().getAssertions();
//		final Proposition FALSE = getFalse(antec.getScopeManager());
//
//		@SuppressWarnings("unchecked")
//		List<Proposition> props = (List<Proposition>) operands;
//		props.add(antecedent = (Proposition) (antics == null || antics.isEmpty() 
//				? FALSE : antics.unwrap()));
//		props.add(consequent = (Proposition) (consqs == null || consqs.isEmpty() 
//				? FALSE : consqs.unwrap()));
//	}
	
	

	/**
	 * Null antecedent/consequent should be treated as unknown one.
	 * 
	 * @param p1
	 * @param p2
	 * @return
	 */
	public static Proposition get(Proposition p1, Supplier<Proposition> p2) {
		return from(Operator.Imply, p1, p2, () -> {
//			guardImply();
			return new Imply(p1, p2.get());
//			unguardImply();
		});
	}
	
//	public Iterable<Proposition> getPropositions() {
//		return Collections.singleton(this);
//	}
	
//	public boolean guardsImply() {return guardsImply;}
//	private void guardImply() {guardsImply = true;}
//	private void unguardImply() {guardsImply = false;}
	
	/**
	 * SE = Antecedent.SE -> Consequent.SE
	 *  
	 * TODO? SE = (Antecedent && Antecedent.SE) -> (Consequent && Consequent.SE) 
	 */
	@Override
	protected <OT extends Expression> boolean cacheOperandDirectSideEffect(
			final OT oprd)
			throws ClassCastException {
		assert consequent != null;
		final VODConditions cse = consequent.getSideEffect();
		if (cse == null || cse.isEmpty()) 
			andSideEffect(()-> antecedent.getSideEffect());
		else 
			andSideEffect(()-> antecedent.getSideEffect().imply(cse));
		return false;
		
//		try {
////			andSideEffect(()-> antecedent);
//		} catch (Exception e) {
//			if (e instanceof ClassCastException) throw (ClassCastException) e;
//			return throwUnhandledException(e);
//		}
	}

	

	/**
	 * (A -> B) /\ A
	 * = (~A \/ B) /\ A
	 * = (~A /\ A) \/ (B /\ A)
	 * = B /\ A
	 * 
	 * (((A /\ B) \/ C) -> D) /\ A
	 * = (~((A /\ B) \/ C) \/ D) /\ A
	 * = ((~(A /\ B) /\ ~C) \/ D) /\ A
	 * = (((~A \/ ~B) /\ ~C) \/ D) /\ A
	 * = ((~A /\ ~C) \/ (~B /\ ~C) \/ D) /\ A
	 * = (~A /\ ~C /\ A) \/ (~B /\ ~C /\ A) \/ (D /\ A)
	 * = (~B /\ ~C /\ A) \/ (D /\ A)
	 * = ((~B /\ ~C) \/ D) /\ A
	 * = (~(B \/ C) \/ D) /\ A
	 * = ((B \/ C) -> D) /\ A
	 * 
	 * (B -> A) /\ A
	 * = (~B \/ A) /\ A
	 * = A
	 * 
	 * (B -> (A /\ C)) /\ A
	 * = (~B \/ (A /\ C)) /\ A
	 * = (~B \/ A) /\ (~B \/ C) /\ A
	 * = (~B \/ C) /\ A
	 * = (B -> C) /\ A
	 * 
	 * ((A \/ C) -> B) /\ A
	 * = (~(A \/ C) \/ B) /\ A
	 * = ((~A /\ ~C) \/ B) /\ A
	 * = (~A \/ B) /\ (~C \/ B) /\ A
	 * = ((~A /\ A) \/ (B /\ A)) /\ (~C \/ B)
	 * = B /\ A /\ (~C \/ B)
	 * = B /\ A
	 * 
	 * (B -> Forall(C /\ (D -> (A /\ E)))) /\ A
	 * = (~B \/ Forall[C /\ (~D \/ (A /\ E))]) /\ A
	 * = (~B \/ [Forall(C) /\ Forall(~D \/ (A /\ E))]) /\ A	...??(X0\/Y0)/\(X1\/Y1)/\.../\(Xn\/Yn)
	 * = ignoresDependency
	 * 
	 * @see ompca.condition.Proposition#andByReduce(ompca.condition.Proposition)
	 */
	protected Proposition andByReduce(Proposition p2) {

		final Supplier<Proposition> p2s = ()-> p2;

		// (A -> B) /\ A = B /\ A
		if (antecedent.equals(p2)) return consequent.and(p2s);

		Proposition newAntec = null;
		boolean isReduced = false;

		/*
		 * ((A /\ B) -> C) /\ A
		 * = (~(A /\ B) \/ C) /\ A
		 * = (~A \/ ~B \/ C) /\ A
		 * = (~A /\ A) \/ (~B /\ A) \/ (C /\ A)
		 * = (~B /\ A) \/ (C /\ A)
		 * = (~B \/ C) /\ A
		 * = (B -> C) /\ A
		 * 
		 * ((B /\ (C \/ (A /\ D))) -> E) /\ A
		 * = (~(B /\ (C \/ (A /\ D))) \/ E) /\ A
		 * = (~B \/ ~(C \/ (A /\ D)) \/ E) /\ A
		 * = (~B \/ (~C /\ ~(A /\ D)) \/ E) /\ A
		 * = (~B \/ (~C /\ (~A \/ ~D)) \/ E) /\ A
		 * = (~B \/ (~C /\ ~A) \/ (~C /\ ~D) \/ E) /\ A
		 * = (~B /\ A) \/ (~C /\ ~A /\ A) \/ (~C /\ ~D /\ A) \/ (E /\ A)
		 * = (~B /\ A) \/ (~C /\ ~D /\ A) \/ (E /\ A)
		 * = (~B \/ (~C /\ ~D) \/ E) /\ A
		 * = (~B \/ ~(C \/ D) \/ E) /\ A
		 * = (~(B /\ (C \/ D)) \/ E) /\ A
		 * = ((B /\ (C \/ D)) -> E) /\ A
		 */
		final ReductionOperations ros = new ReductionOperations();
		ros.add("((A && B) -> C) && A = (B -> C) && A",
				Operator.And, (cia, b)-> b.equals(p2), null, (cia, newB)-> And.from(newB));
		ros.add(Operator.Or, null, null, (b, C)-> Or.from(C));
		ros.add("((B && (C || (A && D))) -> E) && A = ((B && (C || D)) -> E) && A",
				Operator.And, (c, d)-> d.equals(p2), null, (c, newD)-> And.from(newD));
		Proposition result = antecedent.reduceByOperands(ros, false);

		List<Proposition> B = new ArrayList<>();	// more scalable than toSet()
		if (result != null) {newAntec = result; isReduced = true;}
		else if (antecedent.getOp() == Operator.Or) {
			List<Proposition> C = new ArrayList<>();	// more scalable than toSet()
			for (Proposition c : antecedent.getPropositions()) {
				// ((A \/ C) -> B) /\ A = B /\ A
				if (c.equals(p2)) return consequent.and(p2s);
				
				// (((A /\ B) \/ C) -> D) /\ A = ((B \/ C) -> D) /\ A
				if (c.getOp() == Operator.And) {
					for (Proposition b : c.getPropositions()) {
						if (b.equals(p2)) isReduced = true; 
						else B.add(b);
					}
					if (isReduced) c = And.from(B);
				}
				C.add(c);
			}
			if (isReduced) newAntec = Or.from(C);
		} 
		if (isReduced) return newAntec.imply(()-> consequent).and(p2s);

		// (B -> A) && A = A
		if (consequent.equals(p2)) return p2;

		ros.clear();
		ros.add("(C -> (A && B)) && A = (C -> B) && A",
				Operator.And, (cic, b)-> b.equals(p2), null, 
				(cic, newB)-> ros.isReduced(2) 
				? ros.getResult(2, 0)
				: (newB.isEmpty() ? p2 : antecedent.imply(()-> And.from(newB)).and(p2s)));	// (C -> A) && A = A
		/*
		 * (B -> (C && (D -> A))) && A
		 * = (~B || (C && (~D || A))) && A
		 * = (~B || (C && ~D) || (C && A)) && A
		 * = (~B && A) || (C && ~D && A) || (C && A && A)
		 * = (~B && A) || (C && ~D && A) || (C && A)
		 * = (~B || (C && ~D) || C) && A
		 * = (~B || C) && A		...(X && Y) || X = X
		 * = (B -> C) && A
		 */
		final Stack<Forall> fs = new Stack<>();
		final List<Forall> fc = new ArrayList<>();
		ros.addPrimDisj(new ReductionOctet(
				"(B -> (C && (D -> A))) && A = (B -> C) && A",
				Operator.Imply, (c, da)-> ((Imply) c).consequent.equals(p2), null, (c, newDA)-> null),
		/*
		 * (B -> (C && Fx(D -> A))) && A
		 * = (~B || (C && Fx(~D || A))) && A
		 * = (~B || (C && (~D1 || A1) && (~D2 || A2) &&...&& (~Dn || An))) && A
		 * = (~B && A) || (C && (~D1 || A1) && (~D2 || A2) &&...&& (~Dn || An) && A)
		 * = (~B && A) || (C && (~D1 || A1) && (~D2 || A2) &&...&& (~Dn || An) && Ex(A))	...given A depends on ONLY x as Fx
		 * = (~B && A) || (C && (~D1 || A1) && (~D2 || A2) &&...&& (~Dn || An) && (A1 || A2 ||...|| An))
		 * = (~B && A) || (C && (~D1 || A1) && (~D2 || A2) &&...&& (~Dn || An) && A1) 
		 * 		|| (C && (~D1 || A1) && (~D2 || A2) &&...&& (~Dn || An) && A2) ||...
		 * 		|| (C && (~D1 || A1) && (~D2 || A2) &&...&& (~Dn || An) && An)
		 * = (~B && A) || (C && A1 && (~D2 || A2) &&...&& (~Dn || An)) 
		 * 		|| (C && (~D1 || A1) && A2 &&...&& (~Dn || An)) ||...
		 * 		|| (C && (~D1 || A1) && (~D2 || A2) &&...&& An)			...(~X || Y) && Y = Y
		 * = (~B && A) || (C && (~T || A1) && (~D2 || A2) &&...&& (~Dn || An)) 
		 * 		|| (C && (~D1 || A1) && (~T || A2) &&...&& (~Dn || An)) ||...
		 * 		|| (C && (~D1 || A1) && (~D2 || A2) &&...&& (~T || An))
		 * = (~B && A) || (C && Fx(D -> A) && D1=T) || (C && Fx(D -> A) && D2=T) ||...|| (C && Fx(D -> A) && Dn=T)
		 * = (~B && A) || (C && Fx(D -> A) && D)
		 */
		new ReductionOctet(
				"(B -> (C && Fx(D -> A))) && A = (~B && A) || (C && Fx(D -> A) && D)	...given A depends on ONLY x as Fx",
				Predicate.Operator.Forall, 
				(c, X)-> {Forall fc_ = (Forall) c; return !(fs.add(fc_) && fc.add(fc_));}, null, null));
		ros.add(Operator.Imply, (X, da)-> ((Imply) X).consequent.equals(p2) && p2.dependsOnTheSame(fs), null,
				(X, da)-> {fs.removeAll(fc); fc.clear(); return X;},
				(X, newDA)-> p2.dependsOnTheSame(fs) 
				? antecedent.not().and(p2s).or(()-> consequent.and(()-> ((Imply) X).antecedent))
				: returnIndependencyException());
		result = consequent.reduceByOperands(ros, false);
		if (result != null) return result;

		ros.clear();
		/*
		 * (B -> Fx((D -> A) && C)) && A
		 * = (~B || Fx((~D || A) && C)) && Ex(A)	...given A depends on ONLY x as Fx
		 * = (~B || ~D1 || A1) && (~B || C1) && (~B || ~D2 || A2) && (~B || C2) &&...&& (~B || ~Dn || An) && (~B || Cn) && 
		 * 		(A1 || A2 ||...|| An)
		 * = ((~B || ~D1 || A1) && (~B || C1) && (~B || ~D2 || A2) && (~B || C2) &&...&& (~B || ~Dn || An) && (~B || Cn) && A1)
		 * 	|| ((~B || ~D1 || A1) && (~B || C1) && (~B || ~D2 || A2) && (~B || C2) &&...&& (~B || ~Dn || An) && (~B || Cn) && A2) 
		 * 	||...|| ((~B || ~D1 || A1) && (~B || C1) && (~B || ~D2 || A2) && (~B || C2) &&...&& (~B || ~Dn || An) && (~B || Cn) && An)
		 * = ((~B || C1) && (~B || ~D2 || A2) && (~B || C2) &&...&& (~B || ~Dn || An) && (~B || Cn) && A1)
		 * 	|| ((~B || ~D1 || A1) && (~B || C1) && (~B || C2) &&...&& (~B || ~Dn || An) && (~B || Cn) && A2) 
		 * 	||...|| ((~B || ~D1 || A1) && (~B || C1) && (~B || ~D2 || A2) && (~B || C2) &&...&& (~B || Cn) && An)	...(X || Y) && Y = Y
		 * = ((~T || A1) && (~B || C1) && (~B || ~D2 || A2) && (~B || C2) &&...&& (~B || ~Dn || An) && (~B || Cn))
		 * 	|| ((~B || ~D1 || A1) && (~B || C1)  && (~T || A2) && (~B || C2) &&...&& (~B || ~Dn || An) && (~B || Cn)) 
		 * 	||...|| ((~B || ~D1 || A1) && (~B || C1) && (~B || ~D2 || A2) && (~B || C2) &&... && (~T || An) && (~B || Cn))
		 * = ((~(B && D1) || A1) && (~B || C1) && (~B || ~D2 || A2) && (~B || C2) &&...&& (~B || ~Dn || An) && (~B || Cn) && (B && D1)=T)
		 * 	|| ((~B || ~D1 || A1) && (~B || C1)  && (~T || A2) && (~B || C2) &&...&& (~B || ~Dn || An) && (~B || Cn)) 
		 * 	||...|| ((~B || ~D1 || A1) && (~B || C1) && (~B || ~D2 || A2) && (~B || C2) &&... && (~T || An) && (~B || Cn))
		 * = ((~B || ((~D1 || A1) && C1 && (~D2 || A2) && C2 &&...&& (~Dn || An) && Cn)) && (B && D1)=T)
		 * 	|| ((~B || ~D1 || A1) && (~B || C1)  && (~T || A2) && (~B || C2) &&...&& (~B || ~Dn || An) && (~B || Cn)) 
		 * 	||...|| ((~B || ~D1 || A1) && (~B || C1) && (~B || ~D2 || A2) && (~B || C2) &&... && (~T || An) && (~B || Cn))
		 * = ((~B || Fx((D -> A) && C)) && (B && D1)=T) || ((~B || Fx((D -> A) && C)) && (B && D2)=T) 
		 * 	||...|| ((~B || Fx((D -> A) && C)) && (B && Dn)=T)
		 * = ((~B || Fx((D -> A) && C)) && B && D1) || ((~B || Fx((D -> A) && C)) && B && D2) 
		 * 	||...|| ((~B || Fx((D -> A) && C)) && B && Dn)
		 * = (Fx((D -> A) && C) && B && D1) || (Fx((D -> A) && C) && B && D2) 
		 * 	||...|| (Fx((D -> A) && C) && B && Dn)		...(~X || Y) && X = Y && X
		 * = Fx((D -> A) && C) && B && (D1 || D2 ||...|| Dn)
		 * = Fx((D -> A) && C) && B && D
		 * = ignoresDependency
		 */
		ros.add("(B -> Fx(C && (D -> (A && E)))) && A = ignoresDependency",
				Predicate.Operator.Forall, (Bconsq, X)-> false, null, null);
		ros.add(Operator.And, (X, c)-> false, null, null);
		ros.add(Operator.Imply, null, null, (c, ci)-> ((Imply) c).consequent, null);
		ros.add(Operator.And, (cic, e)-> e.equals(p2), null, 
				(cic, newE)-> {ignoreDependency(Operator.And, p2); return null;});
		result = consequent.reduceByOperands(ros, false);
		if (result != null) return result;
		
		return p2 instanceof Imply ? 
				andByReduce((Imply) p2) : super.andByReduce(p2);
	}
	
	/**
	 * (A -> B) /\ (C -> B)
	 * = (~A \/ B) /\ (~C \/ B)
	 * = ((~A \/ B) /\ ~C) \/ ((~A \/ B) /\ B)
	 * = (~A /\ ~C) \/ (B /\ ~C) \/ (~A /\ B) \/ (B /\ B)
	 * = (~A /\ ~C) \/ ((B /\ ~C) \/ (B /\ ~A)) \/ B
	 * = (~A /\ ~C) \/ (B /\ (~C \/ ~A)) \/ B
	 * = ~(A \/ C) \/ (B /\ ~(C /\ A)) \/ (B /\ T)
	 * = ~(A \/ C) \/ (B /\ (~(C /\ A) \/ T))
	 * = (~A /\ ~C) \/ B
	 * = (A \/ C) -> B
	 * 
	 * (A -> B) /\ (A -> C)
	 * = (~A \/ B) /\ (~A \/ C)
	 * = ~A \/ (B /\ C)
	 * = A -> (B /\ C)
	 * 
	 * (A -> B) /\ (C -> (D /\ (A -> E)))
	 * = (~A \/ B) /\ (~C \/ (D /\ (~A \/ E)))
	 * = (~A \/ B) /\ (~C \/ (D /\ ~A) \/ (D /\ E))
	 * = ((~A \/ B) /\ ~C) \/ ((~A \/ B) /\ D /\ ~A) \/ ((~A \/ B) /\ D /\ E)
	 * = ((~A \/ B) /\ ~C) \/ (D /\ ~A) \/ ((~A \/ B) /\ D /\ E)
	 * 		...(X \/ Y) /\ Z /\ X = X /\ Z		X Y Z | (X\/Y)/\Z/\X	X/\Z
	 * 											0 0 0 |	0				0
	 * 											0 0 1 |	0				0
	 * 											0 1 0 |	0				0
	 * 											0 1 1 |	0				0
	 * 											1 0 0 |	0				0
	 * 											1 0 1 |	1				1
	 * 											1 1 0 |	0				0
	 * 											1 1 1 |	1				1
	 * = (~A /\ ~C) \/ (B /\ ~C) \/ (D /\ ~A) \/ (~A /\ D /\ E) \/ (B /\ D /\ E)
	 * = (~A /\ ~C) \/ (B /\ ~C) \/ (D /\ ~A) \/ (B /\ D /\ E)	...X \/ (X /\ Y) = X
	 * 																X Y | X\/(X/\Y)
	 * 																0 0 |	0
	 * 																0 1 |	0
	 * 																1 0 |	1
	 * 																1 1 |	1
	 * = ??((~A \/ B) /\ ~C) \/ (D /\ (~A \/ (B /\ E)))
	 * = ((A -> B) /\ ~C) \/ (D /\ (A -> (B /\ E)))
	 * = ??(~A /\ (~C \/ D)) \/ (B /\ (~C \/ (D /\ E)))
	 * = (~A /\ (C -> D)) \/ (B /\ (C -> (D /\ E)))
	 * 
	 * (A -> B) /\ (C -> (((A /\ D) -> E) /\ F))
	 * = (~A \/ B) /\ (~C \/ ((~(A /\ D) \/ E) /\ F))
	 * = (~A \/ B) /\ (~C \/ ((~A \/ ~D \/ E) /\ F))
	 * = (~A \/ B) /\ (~C \/ (~A /\ F) \/ (~D /\ F) \/ (E /\ F))
	 * = ((~A \/ B) /\ ~C) \/ ((~A \/ B) /\ ~A /\ F) \/ ((~A \/ B) /\ ~D /\ F) \/ ((~A \/ B) /\ E /\ F)
	 * = ((~A \/ B) /\ ~C) \/ (~A /\ F) \/ ((~A \/ B) /\ ~D /\ F) \/ ((~A \/ B) /\ E /\ F)
	 * = (~A /\ ~C) \/ (B /\ ~C) \/ (~A /\ F) \/ (~A /\ ~D /\ F) \/ (B /\ ~D /\ F) \/ (~A /\ E /\ F) \/ (B /\ E /\ F)
	 * = (~A /\ (~C \/ F \/ (~D /\ F) \/ (E /\ F))) \/ (B /\ (~C \/ (~D /\ F) \/ (E /\ F)))
	 * = (~A /\ (~C \/ F)) \/ (B /\ (~C \/ ((~D \/ E) /\ F)))
	 * 		...	X \/ Y \/ (X /\ Z) = X \/ Y		X Y Z | X\/Y\/(X/\Z)	X\/Y
	 * 											0 0 0 |	0				0
	 * 											0 0 1 |	0				0
	 * 											0 1 0 |	1				1
	 * 											0 1 1 |	1				1
	 * 											1 0 0 |	1				1
	 * 											1 0 1 |	1				1
	 * 											1 1 0 |	1				1
	 * 											1 1 1 |	1				1
	 * = ??((C -> F) -> A) -> (B /\ (C -> ((D -> E) /\ F)))
	 * = (~A /\ ~C) \/ (~A /\ F) \/ (B /\ ~C) \/ (B /\ ~D /\ F) \/ (B /\ E /\ F)
	 * = (~A /\ ~C) \/ (~A /\ F) \/ (B /\ ~C) \/ ((B /\ F) /\ (~D \/ E))
	 * = ((~A /\ ~C) \/ (~A /\ F) \/ (B /\ ~C) \/ (B /\ F)) /\ 
	 * 		((~A /\ ~C) \/ (~A /\ F) \/ (B /\ ~C) \/ (~D \/ E))
	 * = (~A \/ B) /\ (~C \/ F) /\ (((~A \/ B) /\ ~C) \/ (~A /\ F) \/ ~D \/ E)
	 * = (~A \/ B) /\ (~C \/ F) /\ (~C \/ (~A /\ F) \/ ~D \/ E)
	 * 		...X /\ Y /\ ((X /\ Z) \/ W) = X /\ Y /\ (Z \/ W) 
	 * 			X Y Z W | X/\Y/\((X/\Z)\/W)	X/\Y/\(Z\/W)	X/\Y/\Z
	 * 			0 0 0 0 |	0				0				0
	 * 			0 0 0 1 |	0				0				0
	 * 			0 0 1 0 |	0				0				0
	 * 			0 0 1 1 |	0				0				0
	 * 			0 1 0 0 |	0				0				0
	 * 			0 1 0 1 |	0				0				0
	 * 			0 1 1 0 |	0				0				0
	 * 			0 1 1 1 |	0				0				0
	 * 			1 0 0 0 |	0				0				0
	 * 			1 0 0 1 |	0				0				0
	 * 			1 0 1 0 |	0				0				0
	 * 			1 0 1 1 |	0				0				0
	 * 			1 1 0 0 |	0				0				0
	 * 			1 1 0 1 |	1				1				0*
	 * 			1 1 1 0 |	1				1				1
	 * 			1 1 1 1 |	1				1				1
	 * = (~A \/ B) /\ (~C \/ F) /\ (((~C \/ ~A) /\ (~C \/ F)) \/ ~D \/ E)
	 * = (~A \/ B) /\ (~C \/ F) /\ (~C \/ ~A \/ ~D \/ E)
	 * = (A -> B) /\ (C -> F) /\ ((C /\ A) -> (D -> E))
	 * 		... ~A	~C	| formula				B F	| formula
	 * 			0	0	| B /\ F /\ (~D \/ E)	0 0 | ~A /\ ~C /\ (~C \/ ~A \/ ~D \/ E) = ~A /\ ~C 
	 * 													...X/\Y/\(X\/Z) = X/\Y 
	 * 			0	1	| B						0 1 | ~A /\ (~C \/ ~A \/ ~D \/ E) = ~A
	 * 			1	0	| F						1 0 | ~C /\ (~C \/ ~A \/ ~D \/ E) = ~C
	 * 			1	1	| 1						1 1 | ~C \/ ~A \/ ~D \/ E
	 * 
	 * 			~A	B	~C	F | formula = ~A/\C/\~F \/ A/\B/\(~C \/ F/\(~D\/E))
	 * 			0	0	0	0 | 0		= ~A/\C/\~F \/ A/\B/\~C \/ A/\B/\F/\(~D\/E)
	 * 			0	0	0	1 |	0
	 * 			0	0	1	0 | 0
	 * 			0	0	1	1 | 0
	 * 			0	1	0	0 | 0
	 * 			0	1	0	1 | ~D \/ E
	 * 			0	1	1	0 | 1
	 * 			0	1	1	1 | 1
	 * 			1	0	0	0 | 0
	 * 			1	0	0	1 | 1
	 * 			1	0	1	0 | 1
	 * 			1	0	1	1 | 1
	 * 			1	1	0	0 | 0
	 * 			1	1	0	1 | 1
	 * 			1	1	1	0 | 1
	 * 			1	1	1	1 | 1
	 * = ((~A \/ B) /\ (~C \/ F) /\ ~C) \/ ((~A \/ B) /\ (~C \/ F) /\ ~A) 
	 * 		\/ ((~A \/ B) /\ (~C \/ F) /\ (~D \/ E))
	 * = ((~A \/ B) /\ ~C) \/ ((~C \/ F) /\ ~A) \/ ((~A \/ B) /\ (~C \/ F) /\ (~D \/ E))
	 * 		...(X \/ Y) /\ Z /\ X = X /\ Z
	 * = ((~A \/ B) /\ ~C) \/ ((~C \/ F) /\ ~A) \/ ((~A \/ B) /\ (~C \/ F) /\ (~D \/ E))
	 * = ??(~A /\ ~C) \/ (~A /\ F) \/ (B /\ ~C) \/ ((B /\ F) /\ (B /\ F /\ ~(~D \/ E)))
	 * 		... B D E F | B/\F	B/\F/\(~D\/E) B/\F/\~(~D\/E)	??(B/\F)/\(B/\F/\ ~(~D\/E))
	 * 			0 0 0 0 |	0	0				0				??
	 * = ??((~A \/ B) /\ (~C \/ F)) /\ ((~A \/ B) /\ (~C \/ F) /\ B /\ F /\ ~(~D \/ E))
	 * = ??((~A \/ B) /\ (~C \/ F)) /\ (B /\ F /\ ~(~D \/ E))	...X/\Y/\(X\/Z) = X/\Y
	 * = ??(~A \/ B) /\ (~C \/ F) /\ B /\ F /\ ~(~D \/ E)
	 * = ??B /\ F /\ D /\ ~E
	 * 		... B D E F | B/\F/\D/\~E	formula
	 * 			0 0 0 0 |	0			~A /\ ~C
	 * 			0 0 0 1 |	0			(A -> B) /\ (C -> (((A /\ D) -> E) /\ F))
	 * 
	 * (B -> A) /\ (C -> (D /\ (E -> (F /\ A))))
	 * = (~B \/ A) /\ (~C \/ (D /\ (~E \/ (F /\ A))))
	 * = (~B \/ A) /\ (~C \/ D) /\ (~C \/ ~E \/ F) /\ (~C \/ ~E \/ A)
	 * = ((~B /\ (~C \/ ~E)) \/ A) /\ (~C \/ D) /\ (~C \/ ~E \/ F)
	 * 						  D/\
	 * 		... ~C	D	~E	| (~D\/~E)	formula	= ((~B \/ A) /\ ~(C /\ ~D) /\ ~(C /\ D /\ E)) 
	 * 			0	0	0	|	0		0			\/ (C /\ D /\ E /\ A /\ F)
	 * 			0	0	1	| 	0		0		= ((~B \/ A) /\ (~C \/ D) /\ (~C \/ ~D \/ ~E))
	 * 			0	1	0	| 	0		A /\ F		\/ (C /\ D /\ E /\ A /\ F)
	 * 			0	1	1	| 	1		~B \/ A	= ((~B \/ A) /\ (~C \/ (D /\ (~D \/ ~E))))
	 * 			1	0	0	| 	0		~B \/ A		\/ (C /\ D /\ E /\ A /\ F)
	 * 			1	0	1	| 	0		~B \/ A	= ((~B \/ A) /\ (~C \/ (D /\ ~E)))
	 * 			1	1	0	| 	0		~B \/ A		\/ (C /\ D /\ E /\ A /\ F)
	 * 			1	1	1	| 	1		~B \/ A	= ((~B \/ A) /\ (~C \/ D) /\ (~C \/ ~E))
	 *												\/ (C /\ D /\ E /\ A /\ F)
	 *			= ((~B \/ A) /\ (~C \/ D) /\ ~(C /\ E)) \/ ((C /\ E) /\ D /\ A /\ F)
	 *			= ((B -> A) /\ (C -> D) /\ (C -> ~E)) \/ (A /\ C /\ D /\ E /\ F)
	 *				... A C D E | formula	= ??
	 *					0 0 0 0 | ~B
	 *					0 0 0 1 | ~B
	 *					0 0 1 0 | ~B
	 *					0 0 1 1 | ~B
	 *					0 1 0 0 | 0
	 *					0 1 1 0 | ~B
	 *					0 1 0 1 | 0
	 *					0 1 1 1 | 0
	 *					1 0 0 0 | 1
	 *					1 0 0 1 | 1
	 *					1 0 1 0 | 1
	 *					1 0 1 1 | 1
	 *					1 1 0 0 | 0
	 *					1 1 0 1 | 0
	 *					1 1 1 0 | 1
	 *					1 1 1 1 | F
	 *				...(~X /\ Y) \/ (X /\ Z) = ??	X Y Z | formula
	 *												0 0 0 | 0
	 *												0 0 1 | 0
	 *												0 1 0 | 1
	 *												0 1 1 | 1
	 *												1 0 0 | 0
	 *												1 1 0 | 0
	 *												1 1 1 | 1
	 *												1 0 1 | 1
	 *			= ??
	 * 		...((X /\ Y) \/ Z) /\ U /\ (X \/ V) = ??
	 * 			X | formula			= (X /\ (Y \/ Z) /\ U) \/ (~X /\ Z /\ U /\ V)
	 * 			0 | Z /\ U /\ V 
	 * 			1 | (Y \/ Z) /\ U 
	 * = ??((~B /\ (~C \/ ~E)) \/ A) /\ (~C \/ (D /\ (~E \/ F)))
	 * = (~(B \/ (C /\ E)) \/ A) /\ (~C \/ (D /\ (~E \/ F)))
	 * = ((B \/ (C /\ E)) -> A) /\ (C -> (D /\ (E -> F)))
	 * 
	 * @see ompca.condition.Proposition#andByReduce(ompca.condition.Imply)
	 */
	private Proposition andByReduce(Imply i2) {
		assert i2 != null;

		Proposition i2a = i2.antecedent, i2c = i2.consequent;
		final Supplier<Proposition> consqSp = ()-> consequent;

		/* (A -> B) && (C -> A)
		 * = (~A || B) && (~C || A)
		 * = ((~A || B) && ~C) || ((~A || B) && A)
		 * = (~A && ~C) || (B && ~C) || (~A && A) || (B && A)
		 * = (~A && ~C) || (B && ~C) || (B && A)
		 * = ~(A || C) || (B && (~C || A))
		 * 
		 * = (C -> B) && ~(~A && B && C) && ~(A && ~B && ~C)
		 * = (C -> B) && (A || ~B || ~C) && (~A || B || C)
		 * = (C -> B) && (A || ~(B && C)) && (~A || B || C)
		 * = (C -> B) && ((B && C) -> A) && (A -> (B || C))
		 * 
		 * A | B | C | (C -> A) && (A -> B) | C -> B 
		 * 0 | 0 | 0 |			1			|	1	 
		 * 0 | 0 | 1 |			0			|	0	 
		 * 0 | 1 | 0 |			1			|	1	 
		 * 0 | 1 | 1 |			0			|	1
		 * 1 | 0 | 0 |			0			|	1
		 * 1 | 0 | 1 |			0			|	0
		 * 1 | 1 | 0 |			1			|	1
		 * 1 | 1 | 1 |			1			|	1
		 */
//		if (antecedent.equals(i2c)) return i2a.imply(consqSp);
		
		final Supplier<Proposition> i2cSp = ()-> i2c;
//		if (consequent.equals(i2a)) return antecedent.imply(i2cSp);
		
		// (A -> B) /\ (A -> C) = A -> (B /\ C)
		if (antecedent.equals(i2a)) return antecedent.imply(()-> consequent.and(i2cSp));
		
		// (A -> B) /\ (C -> B) = (A \/ C) -> B
		final Supplier<Proposition> i2aSp = ()-> i2a;
		if (consequent.equals(i2c)) return antecedent.or(i2aSp).imply(consqSp);

		if (i2c.getOp() == Operator.And) {
			boolean isReduced2 = false, isReduced = false, isCiaAnd = false, isCicAnd = false;
			Proposition cia = null, cic = null;
			List<Proposition> C = new ArrayList<>(), D = new ArrayList<>();
			for (Proposition c : ((And) i2c).getPropositions()) {
				if (!isReduced) {
					if (c.getOp() == Operator.Imply) {
						Imply ci = (Imply) c;
						cia = ci.antecedent; cic = ci.consequent;
						
						// (A -> E) /\ (B -> (C /\ (A -> D)))
						// = (~A /\ (B -> C)) \/ (E /\ (B -> (C /\ D)))
						if (antecedent.equals(cia)) {D.add(cic); isReduced = true; continue;} 
						
						isCiaAnd = cia.getOp() == Operator.And;
						isCicAnd = cic.getOp() == Operator.And;
						if (isCiaAnd || isCicAnd) {
							// (A -> E) /\ (B -> (C /\ ((A /\ D) -> F)))
							// = (A -> E) /\ (B -> C) /\ ((A /\ B) -> (D -> F))
							And ciAnd = (And) (isCiaAnd ? cia : cic);
							// (E -> A) /\ (B -> (C /\ (F -> (D /\ A))))
							// = ((E -> A) /\ (B -> C) /\ (B -> ~F)) \/ (A /\ B /\ C /\ D /\ F)
							Proposition A = isCiaAnd ? antecedent : consequent;
							for (Proposition d : ciAnd.getPropositions()) {
								if (A.equals(d)) {isReduced2 = true; if (isCicAnd) break;}
								else D.add(d);
							} 
							if (isReduced2) continue;
						}
					}
				}
				C.add(c);	// not else, for the inner else above
			}
			
			final Supplier<Proposition> i2aiC = ()-> i2a.imply(()-> And.from(C));
			if (isReduced) {
				D.addAll(C);
				return antecedent.not().and(i2aiC)
						.or(()-> consequent.and(()-> i2a.imply(()-> And.from(D))));
			}
			if (isReduced2) {
				final Proposition prop = and(i2aiC), cia_ = cia, cic_ = cic;
				final Supplier<Proposition> cicSp = ()-> cic_;
				return isCiaAnd
						// = ... /\ ((A /\ B) -> (D -> F))
						? prop.and(()-> antecedent.and(i2aSp).imply(
								()-> And.from(D).imply(cicSp)))
						// = (... /\ (B -> ~F)) \/ (A /\ B /\ C /\ D /\ F)
						: prop.and(()-> i2a.imply(()-> cia_.not())).or(
								()-> i2a.and(C).and(()-> cia_).and(cicSp));
			}
		}
		return null;
	}
	
	
	
	/**
	 * ((A \/ B) -> C) \/ A
	 * = ~(A \/ B) \/ C \/ A
	 * = (~A /\ ~B) \/ C \/ A
	 * = (~A \/ C \/ A) /\ (~B \/ C \/ A)
	 * = ~B \/ C \/ A
	 * 
	 * (B -> A) \/ A
	 * = ~B \/ A \/ A
	 * = B -> A
	 * 
	 * (C -> (A /\ B)) \/ A
	 * = ~C \/ (A /\ B) \/ A
	 * = ~C \/ A
	 * = C -> A
	 * 
	 * @see ompca.condition.Proposition#orByReduce(ompca.condition.Proposition)
	 */
	protected Proposition orByReduce(Proposition p2) {
		if (p2 == null) throwNullArgumentException("p2");
		
		final Supplier<Proposition> p2sp = ()-> p2;
		if (antecedent != null && antecedent.getOp() == Operator.Or) {
			List<Proposition> B = new ArrayList<>();
			boolean isReduced = false;
			for (Proposition b : antecedent.getPropositions()) {
				// ((A \/ B) -> C) \/ A = ~B \/ C \/ A
				if (b.equals(p2)) isReduced = true;
				else B.add(b);
			}
			if (isReduced) return Or.from(B).not().or(()-> consequent).or(p2sp);
		}

		if (consequent != null) {
			// (B -> A) \/ A = B -> A
			if (consequent.equals(p2)) return this;
			
			if (consequent.getOp() == Operator.And) 
				for (Proposition b : consequent.getPropositions()) 
					// (C -> (A /\ B)) \/ A = C -> A
					if (b.equals(p2)) return antecedent.imply(p2sp);
		}
		
		return super.orByReduce(p2);
	}


	
	/**
	 * Supporting both binary and N-ary serial implication.
	 * 
	 * (﻿A -> B) -> B
	 * = ~(~A \/ B) \/ B
	 * = (A /\ ~B) \/ B
	 * = (A \/ B) /\ (~B \/ B)
	 * = (A \/ B) /\ T
	 * = A \/ B
	 * 
	 * (﻿A -> B) -> (B -> C)
	 * = ~(﻿~A \/ B) \/ (~B \/ C)
	 * = (A /\ ~B) \/ ~B \/ C
	 * = (A \/ ~B \/ C) /\ (~B \/ ~B \/ C)
	 * = (A \/ ~B \/ C) /\ (~B \/ C)
	 * = (A \/ ~B \/ C) /\ (F \/ ~B \/ C)
	 * = (A /\ F) \/ ~B \/ C
	 * = ~B \/ C
	 * = B -> C
	 * 
	 * @see ompca.condition.Proposition#implyByReduce(ompca.condition.Proposition)
	 */
	protected Proposition implyByReduce(Proposition consq) {
//		Proposition imply1 = super.imply(consq);
//		if (!(imply1.unwrapOnce() instanceof Imply)) return imply1;
		
		if (consequent != null) {
			if (consequent.equals(consq)) return antecedent.or(()-> consequent);
			if (consq.getOp() == Operator.Imply && 
					consequent.equals(((Imply) consq).antecedent)) return consq;
//			else antecedent = this;			// binary implication update
			
		} else {
			// n-ary implication update if consq.op == Operator.Imply
			consequent = consq;
			add(consq);	
		}
		
		return this;
	}
	
	
	
	/**
	 * A factory delegate method to ensure both antecedent and consequent are optimized.
	 * 
	 * (A -> D) -> (C /\ (B -> (E /\ (A -> F))))
	 * = ~(~A \/ D) \/ (C /\ (~B \/ (E /\ (~A \/ F))))
	 * = (A /\ ~D) \/ (C /\ (~B \/ (E /\ ~A) \/ (E /\ F)))
	 * = (A /\ ~D) \/ (C /\ ~B) \/ (C /\ E /\ ~A) \/ (C /\ E /\ F)
	 * 		...exhaustive (A /\ X) \/ (~A /\ Y) 
	 * 			= (X \/ Y) /\ ~(~A /\ X /\ ~Y) /\ ~(A /\ ~X /\ Y) 
	 * 			= (X \/ Y) /\ (A \/ ~X \/ Y) /\ (~A \/ X \/ ~Y) 
	 * 			= ??(X \/ Y) /\ (A \/ ~X \/ Y) /\ (~A \/ X \/ ~Y) 
	 * 				A X Y | ~A	X \/ Y	(A /\ X) \/ (~A /\ Y)
	 * 				0 0 0 | 1	0		Y/0
	 * 				0 0 1 | 1	1		Y/1
	 * 				0 1 0 | 1	1		Y/0*
	 * 				0 1 1 | 1	1		Y/1
	 * 				1 0 0 | 0	0		X/0
	 * 				1 0 1 | 0	1		X/0*
	 * 				1 1 0 | 0	1		X/1
	 * 				1 1 1 | 0	1		X/1
	 * = ??~D \/ (C /\ E) \/ (C /\ ~B) \/ (C /\ E /\ F)
	 * 
	 * (A -> D) -> (B /\ (Forall x A(x) -> C(x)))
	 * = (A -> D) -> (B /\ Fx(A->C))
	 * 		...when the goal is to make A/Fx(A->C) a singleton
	 * 				Y:		  			Z:		W:		formula:
	 * 			A D Fx(A->C)| Ex(A/\~C)	A->D	B/\Y	Z->W 		A\/Y
	 * 			0 0 0		|	1		-		-		-			-
	 * 			0 0 1		|	0		1		B		B			1
	 * 			0 1	0		|	1		-		-		-			-
	 * 			0 1	1		|	0		1		B		B			1
	 * 			1 0	0		|	1		0		0		1			1
	 * 			1 0 1		|	0		0		B		1			1
	 * 			1 1 0 		|	1		1		0		0			1
	 * 			1 1 1		|	0		1		B		B			1
	 * = (A /\ ~D) \/ (B /\ Fx(A->C))
	 * = ((A /\ ~D) \/ B) /\ ((A /\ ~D) \/ Fx(A->C))
	 * = (A \/ B) /\ (~D \/ B) /\ (A \/ Fx(A->C)) /\ (~D \/ Fx(A->C))
	 * = (A \/ B) /\ (~D \/ B) /\ (~D \/ Fx(A->C))
	 * 		...when the goal is to make A/Fx(A->C) a singleton
	 * 			  Y:		  			Z:(A\/B)	formula:
	 * 			A Fx(A->C)	| Ex(A/\~C)	/\(~D\/Y)	Z/\(D->B)
	 * 			0 0			|	1		-			-
	 * 			0 1			|	0		B			B
	 * 			1 0 		|	1		~D			~D
	 * 			1 1			|	0		1			~D\/B
	 * = ??(A \/ B) /\ (~D \/ (B /\ Fx(A->C)))
	 * = ??(A \/ B) /\ (D -> (B /\ Fx(A->C)))
	 * = ??(A /\ (D -> (B /\ Fx(A->C)))) \/ B
	 * 
	 * (A -> D) -> (B /\ Fx(C -> Fy(A -> E)))
	 * = ??(A -> D) -> (B /\ Fx(C -> Fy(A -> E)))
	 * 		...making A/Fy(A->E) a singleton
	 * 			  Y:		  			X:			formula:
	 * 			A Fy(A->E)	| Ey(A/\~E)	Fx(C->Y)	(A->D)->(B/\X)
	 * 			0 0			|	1		-			-
	 * 			0 1			|	0		1			B
	 * 			1 0 		|	1		Fx(~C)		D->(B/\Fx(~C))
	 * 			1 1			|	0		1			D->B
	 * = (Fy(A->E) /\ ((A -> D) -> B)) \/ (~Fy(A->E) /\ ((A -> D) -> (B /\ Fx(~C))))	...exhaustive Fy
	 * = (Fy(A->E) /\ (~(~A \/ D) \/ B)) \/ (~Fy(A->E) /\ (~(~A \/ D) \/ (B /\ Fx(~C))))
	 * = (Fy(A->E) /\ ((A /\ ~D) \/ B)) \/ (~Fy(A->E) /\ ((A /\ ~D) \/ (B /\ Fx(~C))))
	 * = (Fy(A->E) /\ (A \/ B) /\ (~D \/ B)) \/ (~Fy(A->E) /\ (A \/ (B /\ Fx(~C))) /\ (~D \/ (B /\ Fx(~C))))
	 * = (Fy(A->E) /\ (A \/ B) /\ (~D \/ B)) \/ (~Fy(A->E) /\ (A \/ B) /\ (A \/ Fx(~C)) /\ (~D \/ B) /\ (~D \/ Fx(~C)))
	 * = (A \/ B) /\ (~D \/ B) /\ (Fy(A->E) \/ (~Fy(A->E) /\ (A \/ Fx(~C)) /\ (~D \/ Fx(~C))))
	 * = (A \/ B) /\ (~D \/ B) /\ (Fy(A->E) \/ A \/ Fx(~C)) /\ (Fy(A->E) \/ ~D \/ Fx(~C))
	 * = (A \/ B) /\ (~D \/ B) /\ (Fy(A->E) \/ Fx(~C) \/ (A /\ ~D))
	 * = (A \/ B) /\ (D -> B) /\ (~(A -> D) \/ Fy(A->E) \/ Fx(~C))
	 * 
	 * (D -> A) -> (B /\ Fx(C \/ (A -> E)))
	 * = (D -> A) -> (B /\ Fx(C \/ ~A \/ E))			X:
	 * 		...exhaustive A/Fx(~A):	A Fx(~A)| Ex(A) Fx(C\/~A\/E) formula
	 * 								0	0	|	1		-			-
	 * 								0	1	|	0		1			~D->B
	 * 								1	0	|	1		X			B/\X
	 * 								1	1	|	0		-			-
	 * 									  				 X:
	 * 		...exhaustive A/Fx(A):	A Fx(A)	| Ex(~A) Fx(A->(C\/E)) formula
	 * 								0	0	|	1		??1			~D->B
	 * 								0	1	|	0		-			-
	 * 								1	0	|	1		??X			B/\X
	 * 								1	1	|	0		??-			-
	 * 		??...exhaustive A/Fx(A)..Fx(~A):
	 * 								  X:
	 * 		...exhaustive A/X:		A Fx(A->(C\/E))	| Ex(A) Ex(A/\~(C\/E))	A/\X 
	 * 								0	0			|	0		1			-
	 * 								0	1			|	0		0			0
	 * 								1	0			|	1		1			0
	 * 								1	1			|	1		0			1
	 * = (D -> A) -> (B /\ (Fx(~A) \/ (~Fx(~A) /\ Fx(C \/ ~A \/ E))))
	 * = (D /\ ~A) \/ (B /\ (~A \/ (A /\ Fx(A -> (C \/ E)))))
	 * = ??(D /\ ~A) \/ (B /\ (~A \/ Fx(C \/ E)))
	 * = ??(D /\ ~A) \/ (B /\ ~A) \/ (B /\ Fx(C \/ E))
	 * = ??((D \/ B) /\ ~A) \/ (B /\ Fx(C \/ E))
	 * 
	 * = ??~(~D \/ A) \/ (B /\ Fx(C \/ ~A \/ E))
	 * = ??(D /\ ~A) \/ (B /\ Fx(C \/ ~A \/ E))
	 * 
	 * = ??(D -> A) -> (B /\ ((Fx(A) /\ ..) \/ (~Fx(A) /\ ..)))
	 * 
	 * (D -> A) -> (B /\ (Forall x C(x) -> (Forall y A(y) -> E(y))))
	 * = (D -> A) -> (B /\ Fx(C -> Fy(A->E)))
	 * = (Fy(A->E) /\ ((D -> A) -> B)) \/ (~Fy(A->E) /\ ((D -> A) -> (B /\ Fx(~C))))
	 * 		...when the goal is to make A/Fy(A->E) a singleton
	 * 				Y:		  Z:	W1:			W2:						formula:
	 * 			D A Fy(A->E)| D->A	Y/\(Z->B) 	~Y/\(Z->(B/\Fx(~C)))	W1\/W2 
	 * 			0 0 0		|	1	0			B/\Fx(~C)				B/\Fx(~C)
	 * 			0 0 1		|	1	B			0						B
	 * 			0 1	0		|	1	0			B/\Fx(~C)				B/\Fx(~C)
	 * 			0 1	1		|	1	B			0						B
	 * 			1 0	0		|	0	0			1						1
	 * 			1 0 1		|	0	1	 		0						1
	 * 			1 1 0 		|	1	0			B/\Fx(~C)				B/\Fx(~C)
	 * 			1 1 1		|	1	B			0						B
	 * = (Fy(A->E) /\ B) \/ (~Fy(A->E) /\ B/\Fx(~C)) \/ ~(D->A)	...??exhaustive Fy
	 * = ((Fy(A->E) \/ (~Fy(A->E) /\ Fx(~C))) /\ B) \/ ~(D->A)
	 * = ((Fy(A->E) \/ Fx(~C)) /\ B) \/ ~(D->A)
	 * = (D -> A) -> (B /\ (Fx(~C) \/ Fy(A->E)))
	 * = ??(Fy(A->E) /\ B) \/ (Fx(~C) /\ B) \/ (D/\~A)
	 * = ??
	 * 					Y:
	 * 			D A B C Fy(A->E) | Fx(C->Y) formula
	 * 			0 0 0 0		0	 |	1		0
	 * 			0 0 0 0		1	 |	1		0
	 * 			0 0 0 1		0	 |	0		0
	 * 			0 0 0 1		1	 |	1		0
	 * 			0 0 1 0		0	 |	1		1
	 * 			0 0 1 1		1	 |	1		1
	 * 			0 1 0 0		0	 |	1		0
	 * 			0 1 0 0		1	 |	1		0
	 * 			0 1 0 1		0	 |	0		0
	 * 			0 1 0 1		1	 |	1		0
	 * 			0 1 1 0		0	 |	1		1
	 * 			0 1 1 0		1	 |	1		1
	 * 			0 1 1 1		0	 |	0		0
	 * 			0 1 1 1		1	 |	??1		1
	 * 			??
	 * = ??
	 * 		... Ey(A/\~E) Ey(A) Ey(E)	| ~Ey(A) ~Ey(E)	| Ey(A)/\~Ey(E)	| Ey(~A)/\~Ey(~E)	
	 * 				0		0	0		|	1		1	|	0			|	0
	 * 				0		0	1		|	1		0	|	0			|	~Ey(~E)
	 * 				0		1	0		|	0		1	|	1			|	0	
	 * 				0		1	1		|	0		0	|	0			|	0/1
	 * 				1		0	0		|	1		1	|	-			|	-
	 * 				1		0	1		|	1		0	|	-			|	-
	 * 				1		1	0		|	0		1	|	1			|	0
	 * 				1		1	1		|	0		0	|	-			|	-
	 * 		
	 * 		...Fy(A->E) Ey(E) | Ey(A/\~E) Ey(A) Ey(~A)
	 * 				0		0 |	1			1		
	 * 				0		1 |	1			1		
	 * 				1		0 |	0			0		??0/1
	 * 				1		1 |	0			0/1
	 * 
	 * = (Fy(A->E) /\ (~(~D\/A) \/ B)) \/ (~Fy(A->E) /\ (~(~D\/A) \/ (B /\ Fx(~C))))
	 * = (Fy(~A\/E) /\ ((D/\~A) \/ B)) \/ (~Fy(~A\/E) /\ ((D/\~A) \/ (B /\ Fx(~C))))
	 * = (Fy(~A\/E) /\ ((D/\~A) \/ B)) \/ (Ey(~(~A\/E)) /\ ((D/\~A) \/ (B /\ Fx(~C))))
	 * = (Fy(~A\/E) /\ ((D/\~A) \/ B)) \/ (Ey(A/\~E) /\ ((D/\~A) \/ (B /\ Fx(~C))))
	 * = ??
	 * = ??((A \/ ~A) /\ Fy(~A\/E) /\ ((D/\~A) \/ B)) \/ (A /\ ~E /\ B /\ Fx(~C))
	 * = (Fy(~A\/E) /\ A /\ B) \/ (Fy(~A\/E) /\ ~A /\ (D \/ B)) \/ (A /\ ~E /\ B /\ Fx(~C))
	 * = ((Fy(A->E) \/ (~E /\ Fx(~C))) /\ A /\ B) \/ (Fy(A->E) /\ ~A /\ (D \/ B))
	 * 		... A	E	X:Fx(~C)	Ex(A)->Ex(E)	Ex(A->E)	Y:Fy(A->E)	(Y\/(~E/\X))/\A
	 * 			0	0	0				1			1			1			0
	 * 			0	0	1				1			1			1			0
	 * 			0	1	0				1			1			1			0
	 * 			0	1	1				1			1			1			0
	 * 			1	0	0				0			0/1			0			0
	 * 			1	0	1				0			0/1			0			1
	 * 			1	1	0				1			1			0/1			Y
	 * 			1	1	1				1			1			0/1			Y
	 * = ??
	 * = (B /\ ((D -> A) -> Fx(C -> Fy(A->E)))) \/ (~B /\ ~(D -> A)) 
	 * = ??
	 * = ~(~D \/ A) \/ (B /\ (Forall x ~C(x) \/ (Forall y ~A(y) \/ E(y))))
	 * = (D /\ ~A) \/ (B /\ (Forall x ~C(x) \/ (Forall y ~A(y) \/ E(y))))
	 * = ((D /\ ~A) \/ B) /\ ((D /\ ~A) \/ (Forall x ~C(x) \/ (Forall y ~A(y) \/ E(y))))
	 * = (D \/ B) /\ (~A \/ B) /\ (D \/ (Fx ~C(x) \/ (Fy ~A(y) \/ E(y)))) /\ (~A \/ (Fx ~C(x) \/ (Fy ~A(y) \/ E(y))))
	 * = ??(~A \/ (B /\ (Fx ~C(x) \/ (Fy ~A(y) \/ E(y))))) /\ (D \/ B) /\ (D \/ (Fx ~C(x) \/ (Fy ~A(y) \/ E(y))))
	 * 
	 * @param consq
	 * @return
	 */
	protected Proposition implyByReduce(And consq) {
		boolean isReduced = false, isForallFlattened = false, isForallFlattened2 = false; 
		Proposition C = null, bia = null, bic = null;
		List<Proposition> B = new ArrayList<>();
		Set<VariablePlaceholder<?>> bfqs = null;
		
		for (Proposition b : consq.getPropositions()) {
			if (!isReduced) {
				// (A -> D) -> (B /\ (C -> (E /\ (A -> F)))) = ignoresDependency
				if (b instanceof Imply) {
					bic = ((Imply) b).consequent;
					if (bic instanceof And) 
						for (Proposition e : ((And) bic).getPropositions()) 
							if (e instanceof Imply && antecedent.equals(((Imply) e).antecedent)) 
								ignoreDependency(Operator.Imply, consq);
					
				} else if (b instanceof Forall) {
					Forall bf = (Forall) b;
					Expression bfp = bf.getFirstOperand();
					if (bfp instanceof Imply) {
						Imply bi = (Imply) bfp;
						bia = bi.antecedent;
						bic = bi.consequent;
						// (A -> D) -> (B /\ Fx(A -> C)) = ignoresDependency
						if (antecedent.equals(bia)) ignoreDependency(Operator.Imply, consq);
						if (bic.getOp() == Predicate.Operator.Forall) {
							Expression bicp = ((Forall) bic).getFirstOperand();
							if (bicp instanceof Imply) {
								Proposition bicia = ((Imply) bicp).antecedent;
								bfqs = (Set<VariablePlaceholder<?>>) bf.getQuantifiers();
								C = bia;
								// (D -> A) -> (B /\ Fx(C -> Fy(A -> E)))
								// 	= (D -> A) -> (B /\ (Fx(~C) \/ Fy(A->E)))
								if (consequent.equals(bicia)) {
									isForallFlattened = isReduced = true;
									continue;
								} else {
									// (A -> D) -> (B /\ Fx(C -> Fy(A -> E))) 
									//	= (A \/ B) /\ (D -> B) /\ (~(A -> D) \/ Fy(A->E) \/ Fx(~C))
									if (consequent.equals(bicia)) {
										isForallFlattened2 = isReduced = true;
										continue;
									}
								}
							}
						}
					}
				}
			}
			B.add(b);
		}
		
		if (isForallFlattened || isForallFlattened2) {
			final Proposition fnc = Forall.from(bfqs, C.not()), bic_ = bic; 
			final Supplier<Proposition> bicSp = ()-> bic_;

			// (D -> A) -> (B /\ Fx(C -> Fy(A -> E)))
			// = (D -> A) -> (B /\ (Fx(~C) \/ Fy(A->E)))
			if (isForallFlattened) return imply(()-> fnc.or(bicSp).and(B));
			
			// (A -> D) -> (B /\ Fx(C -> Fy(A -> E))) 
			//	= (A \/ B) /\ (D -> B) /\ (~(A -> D) \/ Fy(A->E) \/ Fx(~C))
			if (isForallFlattened2) 
				return antecedent.or(B)
						.and(()-> consequent.imply(()-> And.from(B)))
						.and(()-> not().or(bicSp).or(()-> fnc));
		}
		
		return null;
	}
	
	
	
	/**
	 * ~(A -> B)
	 * = ~(~A \/ B)
	 * = A /\ ~B
	 * 
	 * Modifying the antecedent directly changes the meaning of this Imply to
	 * (A /\ ~B) -> B, which is out of the expectation to general Imply operations.
	 * Therefore we return a new {@link And} here.
	 * 
	 * @see ompca.condition.Proposition#notByReduce()
	 */
	protected Proposition notByReduce() {
		return consequent == null 
				? null
				: antecedent.and(()-> consequent.not());
	}

	
	
	@Override
	public Boolean dependsOn(Expression v) {
		try {
			return Elemental.testsAnySkipNull(
					()-> antecedent.dependsOn(v), 
					()-> consequent.dependsOn(v));
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}


	
//	@Override
//	public String toZ3SmtString(boolean printsVariableDeclaration, boolean printsFunctionDefinition) {
//		if (antecedent == null || consequent == null) return null;
//		else return "(=> " 
//				+ antecedent.toZ3SmtString(false, false) + " " 
//				+ consequent.toZ3SmtString(false, false) + ")";
//	}

}
