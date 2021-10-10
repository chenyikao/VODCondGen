package ompca.vodcg.condition;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.function.Supplier;

import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.ReductionOperations.ReductionOctet;

/**
 * @author Kao, Chen-yi
 *
 */
public class And extends Proposition {

	final static private Map<Set<Proposition>, And> AND_CACHE = new HashMap<>();
	
	/**
	 * Constructor for inheritance or simple but cache-less (no memory saving) construction.
	 * 
	 * @param conjunction - without duplicates and should NOT be empty.
	 * @throws NoSuchElementException - when the conjunction is empty therefore retrieving 
	 * 	no scope managers.
	 */
	protected And(Set<Proposition> conjunction) throws NoSuchElementException {
		this(	conjunction, 
				conjunction.iterator().next().getScopeManager());	// TODO: \/ conjunction.scope 
	}
	
//	/**
//	 * Single operand constructor, not a copy constructor!
//	 * Private constructor for simple but no-memory-saving construction.
//	 * 
//	 * @param prop
//	 */
//	private And(Proposition prop) {
//		this(	new HashSet<>(Collections.singleton(prop)), 
//				prop.getScopeManager(),
//				false);
////		add(prop);
//	}
	
//	/**
//	 * Private constructor for simple but no-memory-saving construction.
//	 * 
//	 * @param leftOperand
//	 * @param rightOperand
//	 */
//	private And(Proposition leftOperand, Proposition rightOperand) {
//		// TODO: left_operand.getScope() \/ right_operand.getScope()
//		this(new HashSet<Proposition>(), leftOperand.getScopeManager(), false);
//		add(leftOperand);
//		add(rightOperand);
//	}
	
	/**
	 * @param conjunction - without duplicates and should NOT be empty.
	 * @param scopeManager
	 * @param initiatesSideEffect
	 */
	private And(Set<Proposition> conjunction, VODCondGen scopeManager) {
		super(	Operator.And, 
				conjunction, 
				scopeManager);
//		for (Proposition p : conjunction) add(p);
	}
	
//	private And(VOPCondGen scopeManager, boolean initiatesSideEffect) {
//		this((ConditionElement) null, scopeManager, initiatesSideEffect);	// lazy scope setting
//	}
	
//	private And(VOPCondGen scopeManager) {
//		this((ConditionElement) null, scopeManager, false);	// lazy scope setting
//	}
	


//	private void init() {
//		props = (Set<Proposition>) operands;
//	}
	
	
	
//	/**
//	 * @param p
//	 * @return
//	 */
//	final private static Proposition get(Proposition p) {
//		assert p != null;
//		
//		Element r = p.reduce();
//		if (r != p) {
//			if (r instanceof Proposition) return get((Proposition) r);
//			VOPCondGen.throwTodoException("Non-proposition: " + r + "!");
//		}
//		
//		// performance bottleneck due to large singletons to compare
////		Set<Proposition> ps = Collections.singleton(p);
////		And result = (And) AndCache.get(ps);
////		if (result != null) return result;
////		
////		AndCache.put(ps, result = new And(p)); 
////		return result;
//		return p instanceof And ? (And) p : new And(p);
//	}
	
	/**
	 * Empty/constant propositions may have contradict semantics and their conjunction
	 * result is left to {@link Proposition#andByReduce(Proposition)}.
	 * 
	 * @param p1
	 * @param p2
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public static Proposition from(Proposition p1, Supplier<Proposition> p2s) {
		return from(Operator.And, p1, p2s, ()-> {
			
			// default hierarchical flattening 
			final Proposition p2 = p2s.get();
			final boolean p1ia = p1.getOp().equals(Operator.And), 
					p2ia = p2.getOp().equals(Operator.And);
			final Set<Proposition> ps = p1ia 		// with set optimization
					? (Set<Proposition>) p1.toSet() 
					: new HashSet<>(Collections.singleton(p1));
			if (p2ia) ps.addAll((Set<Proposition>) p2.toSet());
			else ps.add(p2);
			
			
			And and = AND_CACHE.get(ps);
			if (and == null) AND_CACHE.put(ps, and = new And(ps));
			return and;});
//			return p1ia && p2ia ? get(new ArrayList<>(ps)) : new And(ps);});
	}
	
	/**
	 * Linearization during optimization saves hashing time.
	 * 
	 * @param conjunction
	 * @return
	 */
	final public static Proposition from(List<? extends Proposition> conjunction) {
		if (conjunction == null || conjunction.isEmpty()) 
			return throwNullArgumentException("Empty And?");
		if (conjunction.size() == 1) return conjunction.iterator().next(); 
		
//		if (!(conjunction instanceof Set<?>)) conjunction = new HashSet<>(conjunction);
//		Proposition result = AndCache.get(conjunction);
//		if (result != null) return result;
		
		Proposition merge = null;
		List<Proposition> mergeConj = new ArrayList<>();
		// binary merge reduction
		for (Proposition p : conjunction) {
			if (merge == null) merge = p;
			else {mergeConj.add(from(merge, ()-> p)); merge = null;}
		}
		if (merge != null) mergeConj.add(merge);
		return from(mergeConj);

		// hierarchical And flattening
//		for (int i = 0; i < props.size(); i++) {
//			Proposition andp = props.get(i).and(prop);
//			if (andp instanceof And) {
//				props.remove(i); i--; 
//				for (Proposition andpp : ((And) andp).getPropositions()) props.add(andpp);
//			} else props.set(i, andp);
//		}

//		for (Proposition p : conjunction) result = result == null ? p : get(result, p);
//		AndCache.add(conjunction, result);
//		return result.clone();
	}
	
	public static Proposition fromSkipNull(Proposition p1, Supplier<Proposition> p2) {
		if (p2 == null) return p1;
		return p1 == null
				? p2.get()
				: from(p1, p2);
	}
	
	

//	@Override
//	public Object clone() {
//		And clone = (And) super.clone();
////		clone.props = (Set<Proposition>) clone.operands;
//		return clone;
//	}

	
	
	/**
	 * (A /\ B) /\ A
	 * = A /\ B		
	 * 
	 * ((A \/ C) /\ B) /\ A
	 * = (A \/ C) /\ B /\ A
	 * = B /\ A
	 * 
	 * (((A /\ D) \/ C) /\ B) /\ A
	 * = (A \/ C) /\ (D \/ C) /\ B /\ A
	 * = (D \/ C) /\ B /\ A	... X /\ Y /\ (X \/ Z) = X /\ Y
	 * 
	 * (B /\ (C \/ (((F /\ A) \/ E) /\ D))) /\ A
	 * = (C \/ (((F /\ A) \/ E) /\ D)) /\ B /\ A
	 * = (C \/ ((F \/ E) /\ (A \/ E) /\ D)) /\ B /\ A
	 * = (C \/ F \/ E) /\ (C \/ A \/ E) /\ (C \/ D) /\ B /\ A
	 * = (C \/ F \/ E) /\ (C \/ D) /\ B /\ A
	 * = (C \/ ((F \/ E) /\ D)) /\ B /\ A
	 * 
	 * (B /\ Forall(C -> Forall(D -> A))) /\ A
	 * = (B /\ Forall(C -> Forall(D -> A))) /\ A
	 * = B /\ Forall(C -> [(D0->A0)/\(D1->A1)/\.../\(Dn->An)]) /\ (A0\/A1\/...\/An)
	 * = B /\ Forall(~C \/ [(D0->A0)/\(D1->A1)/\.../\(Dn->An)]) /\ (A0\/A1\/...\/An)
	 * = B /\ ((~C0/\~C1/\.../\~Cn) \/ [(D0->A0)/\(D1->A1)/\.../\(Dn->An)]) /\ (A0\/A1\/...\/An)
	 * = B /\ ((~C0/\~C1/\.../\~Cn) \/ [(~D0\/A0)/\(~D1\/A1)/\.../\(~Dn\/An)]) /\ (A0\/A1\/...\/An)
	 * = B /\ (~C0\/~D0\/A0)/\(~C0\/~D1\/A1)/\.../\(~C0\/~Dn\/An) /\ (A0\/A1\/...\/An) 
	 * 			/\ (~C1\/~D0\/A0)/\(~C1\/~D1\/A1)/\.../\(~C1\/~Dn\/An) /\ (A0\/A1\/...\/An) /\ ...
	 * 			/\ (~Cn\/~D0\/A0)/\(~Cn\/~D1\/A1)/\.../\(~Cn\/~Dn\/An) /\ (A0\/A1\/...\/An)
	 * = ignoresDependency
	 * 
	 * (B /\ Forall(C /\ A)) /\ A
	 * = B /\ Fa[x]C(x) /\ Fa[y]A(y) /\ A										  X/\Y 
	 * = B /\ Fa[x]C(x) /\ (A0/\A1/\.../\An) /\ (A0\/A1\/...\/An)	... X	Y	| /\(X\/Y) = X/\Y
	 * = B /\ Fa[x]C(x) /\ (A0/\A1/\.../\An)							0	0	| 0
	 * = B /\ Forall(C /\ A)											0	1	| 0
	 * 																	1	0	| 0
	 * (B /\ Forall((D -> (E /\ A)) /\ C)) /\ A							1	1	| 1
	 * = (B /\ Forall[(~D \/ [E /\ A]) /\ C]) /\ A
	 * = (B /\ Forall[(~D \/ E) /\ (~D \/ A) /\ C]) /\ A
	 * = B /\ (~D0\/E0) /\ (~D0\/A0) /\ C0 /\ (~D1\/E1) /\ (~D1\/A1) /\ C1 /\ 
	 * 		... /\ (~Dn\/En) /\ (~Dn\/An) /\ Cn /\ (A0\/A1\/...\/An)
	 * = ignoresDependency
	 * 
	 * (B /\ Forall[([E /\ (F -> [A /\ G])] -> D) /\ C]) /\ A
	 * = B /\ Forall[(~[E /\ (~F \/ [A /\ G])] \/ D) /\ C] /\ A
	 * = B /\ Forall[(~[E /\ (~F \/ A) /\ (~F \/ G)] \/ D) /\ C] /\ A
	 * = B /\ Forall[(~E \/ (F /\ ~A) \/ (F /\ ~G) \/ D) /\ C] /\ A
	 * = B /\ Forall[(~E /\ C) \/ (F /\ ~A /\ C) \/ (F /\ ~G /\ C) \/ (D /\ C)] /\ (A0\/A1\/...\/An)
	 * = ignoresDependency
	 * 
	 * ((A -> C) /\ B) /\ A
	 * = (~A \/ C) /\ B /\ A
	 * = ((~A /\ A) \/ (C /\ A)) /\ B
	 * = A /\ B /\ C
	 * 
	 * ((C -> A) /\ B) /\ A				
	 * = (~C \/ A) /\ B /\ A				
	 * = ((~C /\ A) \/ (A /\ A)) /\ B		
	 * = ((~C /\ A) \/ A) /\ B				
	 * = A /\ B
	 * 
	 * ((C -> (A /\ D)) /\ B) /\ A
	 * = (~C \/ (A /\ D)) /\ B /\ A
	 * = (~C \/ A) /\ (~C \/ D) /\ B /\ A
	 * = ((~C /\ A) \/ A) /\ (~C \/ D) /\ B
	 * = A /\ (~C \/ D) /\ B
	 * = A /\ (C -> D) /\ B
	 * 
	 * ((C -> ((E -> A) /\ D)) /\ B) /\ A
	 * = ((~C \/ ((~E \/ A) /\ D)) /\ B) /\ A
	 * = ((~C \/ (~E /\ D) \/ (A /\ D)) /\ B) /\ A
	 * = (~C /\ B /\ A) \/ (~E /\ D /\ B /\ A) \/ (A /\ D /\ B /\ A)
	 * = (~C /\ B /\ A) \/ (~E /\ D /\ B /\ A) \/ (A /\ D /\ B)
	 * = (~C /\ B /\ A) \/ (A /\ D /\ B)	...(X /\ Y) \/ Y = Y
	 * = (~C \/ D) /\ B /\ A
	 * = (C -> D) /\ B /\ A
	 * 
	 * ((C -> ((A -> E) /\ D)) /\ B) /\ A
	 * = ((~C \/ ((~A \/ E) /\ D)) /\ B) /\ A
	 * = (~C \/ (~A /\ D) \/ (E /\ D)) /\ B /\ A
	 * = (~C /\ B /\ A) \/ (~A /\ D /\ B /\ A) \/ (E /\ D /\ B /\ A)
	 * = (~C /\ B /\ A) \/ (E /\ D /\ B /\ A)
	 * = (~C \/ (E /\ D)) /\ B /\ A
	 * = ((C -> (E /\ D)) /\ B) /\ A
	 * 
	 * ((C -> ForallA) /\ B) /\ A
	 * = (~C \/ [A0/\A1/\.../\An]) /\ B /\ (A0\/A1\/...\/An)
	 * = [(~C /\ [A0\/A1\/...\/An]) \/ ([A0/\A1/\.../\An] /\ [A0\/A1\/...\/An])] /\ B
	 * = [(~C /\ [A0\/A1\/...\/An]) \/ (A0/\A1/\.../\An)] /\ B				... X/\Y/\(X\/Y) = X/\Y
	 * = [~C \/ (A0/\A1/\.../\An)] /\ [(A0\/A1\/...\/An) \/ (A0/\A1/\.../\An)] /\ B
	 * = [~C \/ (A0/\A1/\.../\An)] /\ (A0\/A1\/...\/An) /\ B				... X/\Y\/(X\/Y) = X\/Y
	 * = (C -> ForallA) /\ A /\ B
	 * = ignoreDependency
	 * 
	 * ((C -> (D /\ Forall A)) /\ B) /\ A
	 * = (~C \/ [D /\ A0/\A1/\.../\An]) /\ B /\ (A0\/A1\/...\/An)
	 * = ([~C /\ (A0\/A1\/...\/An)] \/ [D /\ A0/\A1/\.../\An /\ (A0\/A1\/...\/An)]) /\ B
	 * = ([~C /\ (A0\/A1\/...\/An)] \/ [D /\ A0/\A1/\.../\An]) /\ B
	 * = (~C \/ [D /\ A0/\A1/\.../\An]) /\ (A0\/A1\/...\/An \/ [D /\ A0/\A1/\.../\An]) /\ B
	 * = (~C \/ [D /\ A0/\A1/\.../\An]) /\ (A0\/A1\/...\/An \/ D) /\ 
	 * 		(A0\/A1\/...\/An \/ [A0/\A1/\.../\An]) /\ B							  	  (X/\Y) 
	 * = (~C \/ [D /\ A0/\A1/\.../\An]) /\ (A0\/A1\/...\/An \/ D) /\ 	......	X Y | \/X\/Y = X\/Y
	 * 		(A0\/A1\/...\/An) /\ B												0 0 | 0
	 * = (~C \/ [D /\ Forall A]) /\ (A \/ D) /\ A /\ B							0 1 | 1
	 * = (~C \/ [D /\ Forall A]) /\ A /\ B				... (X\/Y)/\X = X		1 0 | 1
	 * = (C -> [D /\ Forall A]) /\ A /\ B										1 1 | 1
	 * = ignoreDependency
	 * 
	 * (B /\ ((A /\ C) -> D)) /\ A
	 * = B /\ (~(A /\ C) \/ D) /\ A
	 * = B /\ (~A \/ ~C \/ D) /\ A
	 * = (~A /\ B /\ A) \/ (~C /\ B /\ A) \/ (D /\ B /\ A)
	 * = (~C /\ B /\ A) \/ (D /\ B /\ A)
	 * = B /\ (C -> D) /\ A
	 * 
	 * (B /\ ((C \/ (A /\ D)) -> E)) /\ A
	 * = B /\ (~(C \/ (A /\ D)) \/ E) /\ A
	 * = B /\ ((~C /\ (~A \/ ~D)) \/ E) /\ A
	 * = B /\ ((~C /\ ~A) \/ (~C /\ ~D) \/ E) /\ A
	 * = (~C /\ ~A /\ B /\ A) \/ (~C /\ ~D /\ B /\ A) \/ (E /\ B /\ A)
	 * = (~C /\ ~D /\ B /\ A) \/ (E /\ B /\ A)
	 * = ((~C /\ ~D) \/ E) /\ B /\ A
	 * = (~(C \/ D) \/ E) /\ B /\ A
	 * = ((C \/ D) -> E) /\ B /\ A
	 * 
	 * (B /\ (((D \/ (A /\ E)) /\ C) -> F)) /\ A
	 * = (~((D \/ (A /\ E)) /\ C) \/ F) /\ B /\ A
	 * = (~(D \/ (A /\ E)) \/ ~C \/ F) /\ B /\ A
	 * = ((~D /\ ~(A /\ E)) \/ ~C \/ F) /\ B /\ A
	 * = ((~D /\ (~A \/ ~E)) \/ ~C \/ F) /\ B /\ A
	 * = (~D \/ ~C \/ F) /\ (~A \/ ~E \/ ~C \/ F) /\ B /\ A
	 * = (~D \/ ~C \/ F) /\ ((~A /\ A) \/ (~E /\ A) \/ (~C /\ A) \/ (F /\ A)) /\ B
	 * = (~D \/ ~C \/ F) /\ ((~E /\ A) \/ (~C /\ A) \/ (F /\ A)) /\ B
	 * = (~D \/ ~C \/ F) /\ (~E \/ ~C \/ F) /\ B /\ A
	 * = ((~D /\ ~E) \/ ~C \/ F) /\ B /\ A
	 * = (~(D \/ E) \/ ~C \/ F) /\ B /\ A
	 * = (~((D \/ E) /\ C) \/ F) /\ B /\ A
	 * = B /\ (((D \/ E) /\ C) -> F) /\ A
	 * 
	 * (((D \/ (((G /\ A) \/ F) /\ E)) -> C) /\ B) /\ A
	 * = ((~(D \/ (((G /\ A) \/ F) /\ E)) \/ C) /\ B) /\ A
	 * = ((~(D \/ ((G \/ F) /\ (A \/ F) /\ E)) \/ C) /\ B) /\ A
	 * = ((~((D \/ G \/ F) /\ (D \/ A \/ F) /\ (D \/ E)) \/ C) /\ B) /\ A
	 * = ((~(D \/ G \/ F) \/ ~(D \/ A \/ F) \/ ~(D \/ E) \/ C) /\ B) /\ A
	 * = (((~D /\ ~G /\ ~F) \/ (~D /\ ~A /\ ~F) \/ (~D /\ ~E) \/ C) /\ B) /\ A
	 * = (~D /\ ~G /\ ~F /\ B /\ A) \/ (~D /\ ~A /\ ~F /\ B /\ A) \/ (~D /\ ~E /\ B /\ A) \/ (C /\ B /\ A)
	 * = (~D /\ ~G /\ ~F /\ B /\ A) \/ (~D /\ ~E /\ B /\ A) \/ (C /\ B /\ A)
	 * = ((~D /\ ~G /\ ~F) \/ (~D /\ ~E) \/ C) /\ B /\ A
	 * = (~(D \/ G \/ F) \/ ~(D \/ E) \/ C) /\ B /\ A
	 * = (~((D \/ G \/ F) /\ (D \/ E)) \/ C) /\ B /\ A
	 * = (((D \/ ((G \/ F) /\ E)) -> C) /\ B /\ A
	 * 
	 * (B /\ ((C /\ (A -> D)) -> E)) /\ A
	 * = (~((~A \/ D) /\ C) \/ E) /\ B /\ A
	 * = ((~(~A \/ D) \/ ~C) \/ E) /\ B /\ A
	 * = ((A /\ ~D) \/ ~C \/ E) /\ B /\ A
	 * = (A \/ ~C \/ E) /\ (~D \/ ~C \/ E) /\ B /\ A
	 * = (~D \/ ~C \/ E) /\ B /\ A
	 * = ((D /\ C) -> E) /\ B /\ A
	 * 
	 * (B /\ ((C /\ (D -> A)) -> E)) /\ A
	 * = (B /\ (~(C /\ (~D \/ A)) \/ E)) /\ A
	 * = (~C \/ (D /\ ~A) \/ E) /\ B /\ A
	 * = (~C /\ B /\ A) \/ (D /\ ~A /\ B /\ A) \/ (E /\ B /\ A)
	 * = (~C /\ B /\ A) \/ (E /\ B /\ A)
	 * = (B /\ (C -> E)) /\ A
	 * 
	 * ((((E -> A) /\ D) \/ C) /\ B) /\ A 
	 * = ((((~E \/ A) /\ D) \/ C) /\ B) /\ A 
	 * = (~E \/ A \/ C) /\ (D \/ C) /\ B /\ A 
	 * = (D \/ C) /\ B /\ A	...X /\ Y /\ (X \/ Z) = X /\ Y 
	 * 
	 * (B /\ ((D /\ ((A /\ F) -> E)) -> C)) /\ A
	 * = (B /\ (~(D /\ (~(A /\ F) \/ E)) \/ C)) /\ A
	 * = (B /\ (~(D /\ (~A \/ ~F \/ E)) \/ C)) /\ A
	 * = (B /\ (~D \/ ~(~A \/ ~F \/ E) \/ C)) /\ A
	 * = (B /\ (~D \/ (A /\ F /\ ~E) \/ C)) /\ A
	 * = B /\ (~D \/ C \/ (A /\ F /\ ~E)) /\ A
	 * = B /\ (~D \/ C \/ A) /\ (~D \/ C \/ F) /\ (~D \/ C \/ ~E) /\ A
	 * = B /\ (~D \/ C \/ F) /\ (~D \/ C \/ ~E) /\ A
	 * = B /\ (~D \/ C \/ (F /\ ~E)) /\ A
	 * = B /\ (~D \/ C \/ ~(~F \/ E)) /\ A
	 * = B /\ (~D \/ ~(~F \/ E) \/ C) /\ A
	 * = B /\ (~(D /\ (~F \/ E)) \/ C) /\ A
	 * = B /\ ((D /\ (F -> E)) -> C) /\ A
	 * 
	 * (((D /\ (E -> (F /\ A))) -> C) /\ B) /\ A
	 * = (~(D /\ (~E \/ (F /\ A))) \/ C) /\ B /\ A
	 * = (~D \/ ~(~E \/ (F /\ A)) \/ C) /\ B /\ A
	 * = (~D \/ (E /\ ~(F /\ A)) \/ C) /\ B /\ A
	 * = (~D \/ (E /\ (~F \/ ~A)) \/ C) /\ B /\ A
	 * = (~D \/ (E /\ ~F) \/ (E /\ ~A) \/ C) /\ B /\ A
	 * = (~D /\ B /\ A) \/ (E /\ ~F /\ B /\ A) \/ (E /\ ~A /\ B /\ A) \/ (C /\ B /\ A)
	 * = (~D /\ B /\ A) \/ (E /\ ~F /\ B /\ A) \/ (C /\ B /\ A)
	 * = (~D \/ (E /\ ~F) \/ C) /\ B /\ A
	 * = (~D \/ ~(~E \/ F) \/ C) /\ B /\ A
	 * = (~(D /\ (E -> F)) \/ C) /\ B /\ A
	 * = (((D /\ (E -> F)) -> C) /\ B) /\ A
	 * 
	 * ((((E -> (F /\ A)) /\ D) \/ C) /\ B) /\ A
	 * = ((((~E \/ (F /\ A)) /\ D) \/ C) /\ B) /\ A
	 * = (~E /\ D /\ B /\ A) \/ (F /\ A /\ D /\ B /\ A) \/ (C /\ B /\ A)
	 * = (~E /\ D /\ B /\ A) \/ (F /\ D /\ B /\ A) \/ (C /\ B /\ A)
	 * = ((~E \/ F) /\ D /\ B /\ A) \/ (C /\ B /\ A)
	 * = (((~E \/ F) /\ D) \/ C) /\ B /\ A
	 * = (((E -> F) /\ D) \/ C) /\ B /\ A
	 *
	 * @param p2
	 * @return
	 */
	@SuppressWarnings("unchecked")
	protected Proposition andByReduce(final Proposition p2) {
		if (p2 == null) throwNullArgumentException("proposition");
		
//		Proposition newPropAndP = get(newProp).and(p);
//		if (!(p.equals(newPropAndP))) {
//			propToRemove = p;	// flattening the hierarchical And result
//			propToAdd = newPropAndP;
//			andsAnd = newPropAndP.getOp() == Operator.And;
//			traversedProps.add(newPropAndP);
//			break traverseProps;
//		} else return this;	// p == p /\ newProp ==> newProp == TRUE or p

		boolean isReduced = false;
		final Relation.Operator op2 = p2.getOp();
		final Proposition nA = p2.not();
		List<Proposition> B = new ArrayList<>();
		Proposition result = null;

		B: for (Proposition b : getPropositions()) {
			// (T /\ B) /\ A = B /\ A
			if (b.isTrue()) continue;
			
			// (A /\ B) /\ A = A /\ B
			if (b.equals(p2)) return this;
			
			// optimization by merging with contradiction
			// (~A /\ B) /\ A = F, (F /\ B) /\ A = F
			if (b.equals(nA) || b.isFalse()) return 
					False.from("(~A && B) && A = F, (F && B) && A = F", Operator.And, this, p2);
//			if (bOp == Operator.Not) {
//				Proposition nb = b.not();
//				// (~(A /\ B) /\ (A /\ B) /\ C) = F
//				if (nb.getOp() == Operator.And && containsOperands(nb))
//					for (Expression e : nb.getOperands()) remove(e);
//			}
			
			if (!isReduced) {
				if (op2.equals(Predicate.Operator.Forall)) result = andByReduce((Forall) p2, b);
				else if (op2 instanceof Operator) {
					switch ((Operator) op2) {
					case And:	result = andByReduce((And) p2, b);		break;
					case Or:	result = andByReduce((Or) p2, b); 		break;
					case Imply:	result = andByReduce((Imply) p2, b); 	break;
					case Not:	result = andByReduce((Not) p2, b); 		break;
					default:
					}
				}
				if (result != null) return result;
				
				Relation.Operator bOp = b.getOp();
				List<Proposition> C = new ArrayList<>(), D = new ArrayList<>(), F = new ArrayList<>();
				// flattening hierarchical And: 
				// ((D /\ C) /\ B) /\ A = A /\ B /\ C /\ D
				if (bOp.equals(Operator.And)) {
					B = (List<Proposition>) toList();
					if (B.remove(b) && 
							B.addAll((Collection<? extends Proposition>) ((And) b).toList()) && 
							B.add(p2)) return from(B);
				}
				
				else if (bOp.equals(Operator.Or)) {
					C.clear();
					for (Proposition c : b.getPropositions()) {
						// ((A \/ C) /\ B) /\ A = B /\ A
						if (c.equals(p2)) {isReduced = true; continue B;}
						
						else if (c.getOp() == Operator.And) {
							D.clear(); 
							D: for (Proposition d : c.getPropositions()) {
								// (((A /\ D) \/ C) /\ B) /\ A
								//	= (D \/ C) /\ B /\ A
								if (d.equals(p2)) {isReduced = true; continue;}
								
								Relation.Operator dOp = d.getOp();
								if (dOp == Operator.Or) {
									List<Proposition> E = new ArrayList<>();
									for (Proposition e : d.getPropositions()) {
										/* 
										 * (B && (C || (D && (A || E)))) && A
										 * = B && (C || (D && A) || (D && E)) && A
										 * = (B && A && C) || (B && A && D && A) || (B && A && D && E)
										 * = (B && A && C) || (B && A && D) || (B && A && D && E)
										 * = B && A && (C || D || (D && E))
										 * = B && A && (C || D)				...X || (X && Y) = X
										 * = (B && (C || D)) && A
										 */
										if (e.equals(p2)) {isReduced = true; continue D;}
										
										/*
										 * (B /\ (C \/ (((F /\ A) \/ E) /\ D))) /\ A 
										 * = (C \/ ((F \/ E) /\ D)) /\ B /\ A
										 */
										if (e.getOp().equals(Operator.And)) {
											F.clear();
											for (Proposition f : e.getPropositions()) {
												if (f.equals(p2)) isReduced = true; 
												else F.add(f);
											}
											if (isReduced) e = from(F);
										}
										E.add(e);
									}
									if (isReduced) d = Or.from(E);
								}
								else if (dOp == Operator.Imply) {
									Imply di = (Imply) d; 
									Proposition dic = di.consequent;
									// ((((E -> A) /\ D) \/ C) /\ B) /\ A 
									//	= (D \/ C) /\ B /\ A 
									if (dic.equals(p2)) {isReduced = true; continue;}
									// ((((E -> (F /\ A)) /\ D) \/ C) /\ B) /\ A 
									//	= (((E -> F) /\ D) \/ C) /\ B /\ A
									else if (dic.getOp() == Operator.And) {
										F.clear();
										for (Proposition f : dic.getPropositions()) {
											if (f.equals(p2)) isReduced = true;
											else F.add(f);
										}
										if (isReduced) d = di.antecedent.imply(()-> from(F));
									}
								}
								D.add(d);
							}
							if (isReduced) c = from(D);
						}
						C.add(c);
					}
					if (isReduced) b = Or.from(C);
				}
				
				else bImply: if (bOp.equals(Operator.Imply)) {
					final Imply bi = (Imply) b;
					// ((A -> C) /\ B) /\ A = A /\ C /\ B
					final Proposition bia = bi.antecedent, bic = bi.consequent;
					if (bia.equals(p2)) {b = bic; isReduced = true; break bImply;}
					
					// ((C -> A) /\ B) /\ A = A /\ B
					if (bic.equals(p2)) {isReduced = true; continue;}
					
					final ReductionOperations ros = new ReductionOperations();
					ros.add("(B && ((A && D) -> C)) && A = B && (D -> C) && A",
							Operator.And, (bia_, d)-> d.equals(p2), null, (bia_, newD)-> from(newD));
					ros.add(Operator.Or, null, null, (d, newD) -> Or.from(newD));
					ros.add("(B && (((D || (A && E)) && C) -> F)) && A = B && (((D || E) && C) -> F) && A",
							Operator.And, (d, e)-> e.equals(p2), null, (d, newE)-> from(newE));
					result = bia.reduceByOperands(ros, false);
					final Supplier<Proposition> bicSp = ()-> bic;
					if (result != null) {
						b = result.imply(bicSp); isReduced = true; break bImply;}
					
					else if (bia.getOp().equals(Operator.And)) {
						D.clear();
						for (Proposition d : bia.getPropositions()) {
							if (!isReduced) {
								if (d.getOp() == Operator.Imply) {
									final Imply di = (Imply) d; 
									final Proposition dia = di.antecedent, dic = di.consequent;
									
									// (B /\ ((D /\ (A -> E)) -> C)) /\ A = (B /\ ((E /\ D) -> C)) /\ A
									if (dia.equals(p2)) {d = dic; isReduced = true;}
									
									// (B /\ ((D /\ (E -> A)) -> C)) /\ A = (B /\ (D -> C)) /\ A
									else if (dic.equals(p2)) {isReduced = true; continue;}
									
									// (B /\ ((D /\ ((A /\ F) -> E)) -> C)) /\ A 
									//	= B /\ ((D /\ (F -> E)) -> C) /\ A
									else if (dia.getOp() == Operator.And) {
										F.clear();
										for (Proposition f : dia.getPropositions()) {
											if (f.equals(p2)) isReduced = true;
											else F.add(f);
										}
										if (isReduced) d = from(F).imply(()-> dic);
									}
									// (B /\ ((D /\ (E -> (F /\ A))) -> C)) /\ A 
									//	= (((D /\ (E -> F)) -> C) /\ B) /\ A
									else if (dic.getOp() == Operator.And) {
										F.clear();
										for (Proposition f : dic.getPropositions()) {
											if (f.equals(p2)) isReduced = true;
											else F.add(f);
										}
										if (isReduced) d = dia.imply(()-> from(F));
									}
								}
							}
							D.add(d);
						}
						if (isReduced) {b = from(D).imply(bicSp); break bImply;}
					
					} else {
						ros.clear();
						ros.add(Operator.Or, null, null, (bia_, newC)-> Or.from(newC));
						ros.add("(B && ((C || (A && D)) -> E)) && A = ((C || D) -> E) && B && A", 
								Operator.And, (c, d)-> d.equals(p2), null, (c, newD)-> from(newD));
						ros.add(Operator.Or, null, null, (d, newF)-> Or.from(newF));
						ros.add("(((C || (((G && A) || F) && D)) -> E) && B) && A"
								+ " = (((C || ((G || F) && D)) -> E) && B && A", 
								Operator.And, (f, g)-> g.equals(p2), null, (f, newG)-> from(newG));
						result = bia.reduceByOperands(ros, false);
						if (result != null) {
							b = result.imply(bicSp); isReduced = true; break bImply;}
					}
						
					Relation.Operator bicOp = bic.getOp();
					if (bicOp.equals(Operator.And)) {
						D.clear();
						for (Proposition d : bic.getPropositions()) {
							if (!isReduced) {
								// ((C -> (A /\ D)) /\ B) /\ A = A /\ (C -> D) /\ B
								if (d.equals(p2)) {isReduced = true; continue;} 
								
								else {
									Relation.Operator dOp = d.getOp();
									if (dOp.equals(Operator.Imply)) {
										Imply di = (Imply) d; 
										Proposition dic = di.consequent;
										// ((C -> ((E -> A) /\ D)) /\ B) /\ A 
										//	= (C -> D) /\ B /\ A
										if (dic.equals(p2)) {isReduced = true; continue;}
										
										// ((C -> ((A -> E) /\ D)) /\ B) /\ A
										// = ((C -> (E /\ D)) /\ B) /\ A
										else if (di.antecedent.equals(p2)) {
											isReduced = true; d = dic;}
										
									} else if (dOp.equals(Predicate.Operator.Forall)) 
										// ((C -> (D /\ Forall A)) /\ B) /\ A = ignoreDependency
										ignoreDependency(Operator.And, p2);
								}
							}
							D.add(d);
						}
						if (isReduced) {b = bia.imply(()-> from(D)); break bImply;}
						
					} else if (bicOp == Predicate.Operator.Forall) 
						// ((C -> ForallA) /\ B) /\ A = ignoreDependency
						ignoreDependency(Operator.And, p2);
				}
				
				// (Forall)
				else if (bOp.equals(Predicate.Operator.Forall)) {
					b = andByReduceForall(p2, (Forall) b);
					if (b == this) return this;
					if (b != null) isReduced = true;
				}
			}
			B.add(b);
		}
		
		return isReduced ? p2.and(B) : super.andByReduce(p2);
	}
	

	
//	protected Proposition andByReduce(Or newProp) {
//	for (Proposition p : ((Or) newProp).getPropositions()) props.add(p.not());
//	not();
//}

	private Proposition andByReduce(final And and2, final Proposition b) {
		assert and2 != null && !and2.isEmpty();

		final ReductionOperations ros = new ReductionOperations();
		/*
		 * ((B -> A) /\ C) /\ (D /\ A)
		 * = (~B \/ A) /\ C /\ D /\ A
		 * = C /\ D /\ A	...X /\ Y /\ (X \/ Z) = X /\ Y
		 * 
		 * ((B -> (A /\ C)) /\ D) /\ (E /\ A)
		 * = (A /\ E) /\ (D /\ (B -> (C /\ A)))
		 * = A /\ E /\ D /\ (B -> C)
		 */
		ros.clear();
		ros.add(Operator.And, null, null, (this_, newB)-> and2.and(()-> from(newB)));
		ros.add("((A -> D) && B) && (C && D) = B && C && D",
				Operator.Imply, (b_, ad)-> and2.contains(((Imply) b_).consequent), null, (b_, ad)-> b_, 
				(b_, newAD)-> ros.isReduced(1) ? null : newAD.get(0));	// return null or (A->E)
		ros.add("((A -> (D && E)) && B) && (C && D) = C && D && B && (A -> E)", b_-> ((Imply) b_).consequent, 
				Operator.And, (b_, de)-> and2.contains(de), null, 
				(b_, newE)-> ((Imply) b_).antecedent.imply(()-> from(newE)));
		Proposition result = reduceByOperands(ros, false);
		if (result != null) return result;

		/*
		 * (A /\ B) /\ (C -> A)			(A /\ B) /\ (C -> A) /\ D
		 * = A /\ (B /\ (C -> A))		= A /\ B /\ D
		 * = A /\ B
		 * 
		 * (A /\ B) /\ (C /\ B)		
		 * = A /\ B /\ C			
		 * 
		 * (A /\ B) /\ (C /\ (D -> A))
		 * = A /\ B /\ C /\ (~D \/ A)	...X /\ Y /\ (X \/ Z) = X /\ Y
		 * = (A /\ B) /\ C
		 * 
		 * (A /\ B) /\ (C /\ (D -> (E /\ A)))
		 * = A /\ B /\ C /\ (~D \/ (E /\ A))
		 * = A /\ B /\ C /\ (~D \/ E) /\ (~D \/ A)
		 * = A /\ B /\ C /\ (~D \/ E)
		 * = A /\ B /\ C /\ (D -> E)
		 */
		ros.add("(A && B) && (C && B) = (A && B) && C", 
				Operator.And, (and2_, c)-> c.equals(b), null, (and2_, newC)-> and(from(newC)));	
		ros.add("(A && B) && (C && (D -> B)) = (A && B) && C",
				Operator.Imply, (c, d)-> ((Imply) c).consequent.equals(b), null, (c, d)-> c, (c, newD)-> null);
		ros.add("(A && B) && (C && (D -> (E && B))) = A && B && C && (D -> E)", c-> ((Imply) c).consequent, 
				Operator.And, (c, e)-> e.equals(b), null, 
				(c, newE)-> ((Imply) c).antecedent.imply(()-> from(newE)));	// D -> B
		return and2.reduceByOperands(ros, false);
	}
	
	/**
	 * (A /\ B) /\ A	(A /\ B) /\ (A \/ C)			(A /\ B) /\ (~A \/ C)
	 * = A /\ B			= B /\ ((A /\ A) \/ (A /\ C))	= B /\ ((A /\ ~A) \/ (A /\ C))
	 * 					= B /\ (A \/ (A /\ C))			= (B /\ A) /\ C
	 * 					= B /\ A
	 * 
	 * (A /\ B) /\ (C \/ (D /\ A))
	 * = (A /\ B) /\ (C \/ D) /\ (C \/ A)
	 * = (A /\ B) /\ (C \/ D)
	 * 
	 * (A /\ B) /\ (C \/ (D /\ ~A))
	 * = A /\ B /\ (C \/ D) /\ (C \/ ~A)
	 * = B /\ (C \/ D) /\ ((A /\ C) \/ (A /\ ~A))
	 * = B /\ (C \/ D) /\ A /\ C
	 * = (B /\ A) /\ C
	 * 
	 * (A /\ B) /\ (C \/ (D /\ (E /\ A)))
	 * = (A /\ B) /\ (C \/ ((D /\ E) /\ A))
	 * = (A /\ B) /\ (C \/ (D /\ E))
	 * 
	 * (A /\ B) /\ (C \/ (D /\ (A -> E)))
	 * = A /\ B /\ (C \/ (D /\ (~A \/ E)))
	 * = A /\ B /\ (C \/ (D /\ ~A) \/ (D /\ E))
	 * = (A /\ B /\ C) \/ (A /\ B /\ D /\ ~A) \/ (A /\ B /\ D /\ E)
	 * = (A /\ B /\ C) \/ (A /\ B /\ D /\ E)
	 * = (A /\ B) /\ (C \/ (D /\ E))
	 * 
	 * (A /\ B) /\ (C \/ (D \/ (E /\ A)))
	 * = A /\ B /\ (C \/ D \/ E) /\ (C \/ D \/ A)
	 * = (A /\ B) /\ (C \/ D \/ E)
	 * 
	 * = A /\ B /\ (~C \/ ~D)
	 * = (A /\ B) /\ ~(C /\ D)
	 * 
	 * @param newProp
	 * @param b
	 * @return
	 */
	private Proposition andByReduce(Or newProp, Proposition b) {
		boolean isReduced = false, isReduced2 = false;
		List<Proposition> Cs = new ArrayList<>(), D = new ArrayList<>(), Es = new ArrayList<>();
		for (Proposition c : newProp.getPropositions()) {
			if (!isReduced && !isReduced2) {
				// (A /\ B) /\ (A \/ C) = B /\ A
				if (c.equals(b)) return this;
				
				// (A /\ B) /\ (~A \/ C) = (B /\ A) /\ C
				else if (c.not().equals(b)) {isReduced = true; continue;}
				
				else {
					Relation.Operator cOp = c.getOp();
					if (cOp == Operator.And) {
						D.clear();
						for (Proposition d : ((And) c).getPropositions()) {
							if (!isReduced) {
								Relation.Operator dOp = d.getOp();
								// (A /\ B) /\ (C \/ (D /\ A)) 
								//	= (A /\ B) /\ (C \/ D)
								if (d.equals(b)) {
									isReduced = true; continue;}
								// (A /\ B) /\ (C \/ (D /\ ~A)) 
								//	= (B /\ A) /\ C
								else if (d.not().equals(b)) {
									isReduced2 = true; break;}
								// (A /\ B) /\ (C \/ (D /\ (E /\ A)))
								//	= (A /\ B) /\ (C \/ (D /\ E))
								else if (dOp == Operator.And) {
									Es.clear();
									for (Proposition e : ((And) d).getPropositions()) {
										if (e.equals(b)) isReduced = true;
										else Es.add(e);
									}
									if (isReduced) {
										if (Es.isEmpty()) continue;	// E/\A == A
										d = from(Es);
									}
								}
								// (A /\ B) /\ (C \/ (D /\ (A -> E))) 
								//	= (A /\ B) /\ (C \/ (D /\ E))
								else if (dOp == Operator.Imply) {
									Imply di = (Imply) d;
									if (di.antecedent.equals(b)) {
										isReduced = true; 
										d = di.consequent;
									}
								}
							}
							D.add(d);
						}
						if (isReduced) {
							if (D.isEmpty()) return this;	// D/\A == A
							c = from(D);
						}
						if (isReduced2) continue;
					}
					
					// (A /\ B) /\ (C \/ (D \/ (E /\ A))) 
					//	= (A /\ B) /\ (C \/ D \/ E)
					else if (cOp == Operator.Or) {
						for (Proposition d : ((Or) c).getPropositions()) {
							if (d.getOp() == Operator.And) {
								D.clear(); Es.clear();
								for (Proposition e : ((And) d).getPropositions()) {
									if (e.equals(b)) isReduced = true;
									else Es.add(e);
								}
								if (isReduced) {
									if (Es.isEmpty()) return this; // E/\A == A
									d = from(Es);
								} else break;
							}
							D.add(d);
						}
						if (isReduced) c = Or.from(D);
						else break;
					}
				}
			}
			Cs.add(c);
		}
		return isReduced || isReduced2 ? and(()-> Or.from(Cs)) : null;
	}
	
	/**
	 * (A /\ B) /\ (C -> A)
	 * = A /\ (B /\ (C -> A))
	 * = A /\ B
	 * 
	 * (A /\ B) /\ (C -> (A /\ D))
	 * = A /\ B /\ (~C \/ (A /\ D))
	 * = A /\ B /\ (~C \/ A) /\ (~C \/ D)
	 * = B /\ ((A /\ ~C) \/ (A /\ A)) /\ (~C \/ D)
	 * = B /\ A /\ (~C \/ D)  
	 * = A /\ B /\ (C -> D)
	 *
	 * (A /\ B) /\ (C -> (D /\ (E -> A)))
	 * = A /\ B /\ (~C \/ (D /\ (~E \/ A)))
	 * = A /\ B /\ (~C \/ D) /\ (~C \/ ~E \/ A)...X/\Y/\(X\/Z) = X/\Y
	 * = A /\ B /\ (~C \/ D)
	 * = (A /\ B) /\ (C -> D)
	 * 
	 * (A /\ B) /\ (C -> (D /\ (E -> (F /\ A))))
	 * = A /\ B /\ (~C \/ (D /\ (~E \/ (F /\ A))))
	 * = A /\ B /\ (~C \/ (D /\ (~E \/ F) /\ (~E \/ A)))
	 * = A /\ B /\ (~C \/ D) /\ (~C \/ ~E \/ F) /\ (~C \/ ~E \/ A)
	 * = A /\ B /\ (~C \/ D) /\ (~C \/ ~E \/ F)
	 * = A /\ B /\ (~C \/ (D /\ (~E \/ F))
	 * = (A /\ B) /\ (C -> (D /\ (E -> F))
	 * 
	 * @param p2
	 * @param b 
	 * @return
	 */
	private Proposition andByReduce(Imply p2, Proposition b) {
		boolean isReduced = false, isReduced2 = false;
		
		Proposition ciAntec = p2.antecedent, ciConsq = p2.consequent;
		
		// (A /\ B) /\ (C -> A) = A /\ B
		if (ciConsq.equals(b)) return this;

		if (ciConsq.getOp().equals(Operator.And)) {
			List<Proposition> D = new ArrayList<>(), F = new ArrayList<>();
			Proposition diAntec = null, diConsq = null;
			for (Proposition d : ((And) ciConsq).getPropositions()) {
				if (!isReduced && !isReduced2) {
					// (A /\ B) /\ (C -> (A /\ D)) = A /\ B /\ (C -> D)
					if (d.equals(b)) {isReduced = true; continue;}
					else if (d.getOp() == Operator.Imply) {
						p2 = (Imply) d;
						diAntec = p2.antecedent; diConsq = p2.consequent;
						// (A /\ B) /\ (C -> (D /\ (E -> A)))
						// 	= (A /\ B) /\ (C -> D)
						if (diConsq.equals(b)) {isReduced = true; continue;}
						// (A /\ B) /\ (C -> (D /\ (E -> (F /\ A)))) 
						//	= (A /\ B) /\ (C -> (D /\ (E -> F))
						else if (diConsq.getOp() == Operator.And) {
							for (Proposition f : ((And) diConsq).getPropositions()) {
								if (f.equals(b)) isReduced2 = true;
								else F.add(f);
							}
						}
						// F.size() < diConsq.getPropositions().size()
						if (isReduced2) continue;
					}
				} 
				D.add(d);
			}
			if (isReduced) {
				return and(()-> ciAntec.imply(()-> from(D)));
			}
			if (isReduced2) {
				final Proposition diAntec_ = diAntec;
				return and(()-> ciAntec.imply(()-> from(D)
						.and(()-> diAntec_.imply(()-> from(F)))));
			}
		}
		
		return null;
	}
	
	/**
	 * (A /\ B) /\ ~(C /\ (A -> D))
	 * = (A /\ B) /\ (~C \/ (A /\ ~D))
	 * = A /\ B /\ (~C \/ A) /\ (~C \/ ~D)	...X /\ Y /\ (X \/ Z) = X /\ Y
	 * 											X Y Z | X/\Y/\(X\/Z)	X/\Y
	 * 											0 0 0 |	0				0
	 * 											0 0 1 |	0				0
	 * 											0 1 0 |	0				0
	 * 											0 1 1 |	0				0
	 * 											1 0 0 |	0				0
	 * 											1 0 1 |	0				0
	 * 											1 1 0 |	1				1
	 * 											1 1 1 |	1				1
	 * @param newProp
	 * @param b
	 * @return
	 */
	private Proposition andByReduce(Not newProp, Proposition b) {
		Proposition npn = newProp.not();
		if (npn.getOp() == Operator.And) {
			boolean isReduced = false;
			List<Proposition> C = new ArrayList<>();
			for (Proposition c : ((And) npn).getPropositions()) {
				// (A /\ B) /\ ~(C /\ (A -> D)) = (A /\ B) /\ ~(C /\ D)
				if (c.getOp() == Operator.Imply) {
					Imply ci = (Imply) c;
					if (ci.antecedent.equals(b)) {
						c = ci.consequent; isReduced = true;}
				}
				C.add(c);
			}
			if (isReduced) return and(()-> from(C).not());
		}
		
		return null;
	}
	
	/**
	 * (A /\ B) /\ Forall x C(x)->A(x) = ignoresDependency
	 * 
	 * @param p2
	 * @param b
	 * @return
	 */
	private Proposition andByReduce(Forall p2, Proposition b) {
		Expression fap = p2.getFirstOperand();
		if (fap instanceof Imply) {
			Imply fai = (Imply) fap;
			// (A /\ B) /\ Forall x C(x)->A(x) = ignoresDependency
			if (fai.consequent.equals(b)) ignoreDependency(Operator.And, p2);
		}
		return null;
	}
	
	/**
	 * @param p2
	 * @param b - the beginning proposition for matching and reducing {@link Forall}
	 * @return this if matched p2; null if not
	 */
	protected Proposition andByReduceForall(Proposition p2, Forall b) {
		if (p2 == null) throwNullArgumentException("proposition");
		if (b == null) throwNullArgumentException("forall");
		
		final List<Forall> fs = Arrays.asList(b);
		final Proposition bfp = b.getProposition();

		/*
		 * (B && Fx(A)) && A
		 * = (B && Fx(A)) && Ex(A)	...given A depends on ONLY x as Fx
		 * = B && A1 && A2 &&...&& An && (A1 || A2 ||...|| An)
		 * = B && Fx(A)
		 */
		if (bfp.equals(p2) && p2.dependsOnTheSame(b)) return this;
		
		/*
		 * (B && Fx(C && A)) && A 
		 * = (B && Fx(C) && A) && A		...given A in-depends on x
		 * = (B && Fx(C)) && A
		 * 
		 * (B && Fx(C && A)) && A = this	...given A depends on ONLY x as Fx
		 * 
		 * (B && Fx((D -> A) && C)) && A
		 * = (B && Fx((~D || A) && C)) && Ex(A)
		 * = B && (~D1 || A1) && C1 && (~D2 || A2) && C2 &&...&& (~Dn || An) && Cn && (A1 || A2 ||...|| An)
		 * = (B && (~D1 || A1) && C1 && (~D2 || A2) && C2 &&...&& (~Dn || An) && Cn && A1) || 
		 * 		(B && (~D1 || A1) && C1 && (~D2 || A2) && C2 &&...&& (~Dn || An) && Cn && A2) ||...|| 
		 * 		(B && (~D1 || A1) && C1 && (~D2 || A2) && C2 &&...&& (~Dn || An) && Cn && An)
		 * = (B && A1 && C1 && (~D2 || A2) && C2 &&...&& (~Dn || An) && Cn) || 
		 * 		(B && (~D1 || A1) && C1 && A2 && C2 &&...&& (~Dn || An) && Cn) ||...|| 
		 * 		(B && (~D1 || A1) && C1 && (~D2 || A2) && C2 &&...&& An && Cn)			...(X || Y) && Y = Y
		 * = (B && (~T || A1) && C1 && (~D2 || A2) && C2 &&...&& (~Dn || An) && Cn) || 
		 * 		(B && (~D1 || A1) && C1 && (~T || A2) && C2 &&...&& (~Dn || An) && Cn) ||...|| 
		 * 		(B && (~D1 || A1) && C1 && (~D2 || A2) && C2 &&...&& (~T || An) && Cn)
		 * = (B && Fx((D -> A) && C) && D1=T) || (B && Fx((D -> A) && C) && D2=T) ||...|| 
		 * 		(B && Fx((D -> A) && C) && Dn=T)
		 * = B && Fx((D -> A) && C) && (D1 || D2 ||...|| Dn)
		 * = B && Fx((D -> A) && C) && D
		 * = ignoresDependency
		 */
		Proposition result = andByReduceForallAnd(p2, bfp, fs);
		if (result == this) return this;
		if (result != null) return Forall.from(b.quantifiers, result);
		
		result = andByReduceForall2(p2, bfp, fs);
		if (result != null) return result;
		
		final List<Forall> fas = new ArrayList<>(Arrays.asList(b));
		final ReductionOperations ros = new ReductionOperations();
		/*
		 * (B && Fx(A -> C)) && A
		 * = (B && Fx(~A || C)) && Ex(A)	...given A depends on ONLY x as Fx
		 * = (B && (~A1 || C1) && (~A2 || C2) &&...&& (~An || Cn)) && (A1 || A2 ||...|| An)
		 * = (B && (~A1 || C1) && (~A2 || C2) &&...&& (~An || Cn) && A1) 
		 * 		|| (B && (~A1 || C1) && (~A2 || C2) &&...&& (~An || Cn) && A2) 
		 * 		||...|| (B && (~A1 || C1) && (~A2 || C2) &&...&& (~An || Cn) && An)
		 * = (B && C1 && (~A2 || C2) &&...&& (~An || Cn) && A1) 
		 * 		|| (B && (~A1 || C1) && C2 &&...&& (~An || Cn) && A2) 
		 * 		||...|| (B && (~A1 || C1) && (~A2 || C2) &&...&& Cn && An)	...(~X || Y) && X = (~X && X) || (Y && X) = Y && X
		 * = (B && (~T || T) && (~A2 || C2) &&...&& (~An || Cn) && C1 && A1) 
		 * 		|| (B && (~A1 || C1) && (~T || T) &&...&& (~An || Cn) && C2 && A2) 
		 * 		||...|| (B && (~A1 || C1) && (~A2 || C2) &&...&& (~T || T) && Cn && An)
		 * = (B && Fx(A -> C) && C1=T && C1 && A1=T && A1) || (B && Fx(A -> C) && C2=T && C2 && A2=T && A2) 
		 * 		||...|| (B && Fx(A -> C) && Cn=T && Cn && An=T && An)
		 * = (B && Fx(A -> C)) && ((C1 && A1) || (C2 && A2) ||...|| (Cn && An))
		 * = (B && Fx(A -> C)) && Ex(C && A) = ignoresDependency
		 * 
		 * (B && Fx(A -> C)) && A
		 * = B && Fx(~A || C) && A
		 * = B && (~A || C1) && (~A || C2) &&...&& (~A || Cn) && A	...given A in-depends on x
		 * = B && A && C1 && (~A || C2) &&...&& (~A || Cn) 			...(~X || Y) && X = (~X && X) || (Y && X) = Y && X
		 * = B && A && C1 && C2 &&...&& Cn
		 * = B && A && Fx(C)
		 * 
		 * (Fx(C -> A) && B) && A = ignoresDependency
		 * 
		 * (B && Fx(C -> A)) && A
		 * = B && Fx(~C || A) && A
		 * = B && (~C1 || A) && (~C2 || A) &&...&& (~Cn || A) && A	...given A in-depends on x
		 * = B && A && (~C2 || A) &&...&& (~Cn || A) 				...(~X || Y) && Y = Y
		 * = B && A
		 */
		final ReductionOctet roImply = new ReductionOctet(
				Operator.Imply, 
				(X, ca)-> {Imply xi = (Imply) X; return p2.equals(xi.antecedent) || p2.equals(xi.consequent);}, 
				null, (X, ca)-> ((Imply) X).consequent,
				(X, newX) -> p2.independsOn(fas) ? returnIndependencyException() : ignoreDependency(Operator.And, p2)),
		roForall = new ReductionOctet(
				"(B && Fx(C -> Fy(D -> A))) && A = ignoresDependency	...given A depends on ONLY x and y as Fxy",
				Predicate.Operator.Forall, (Fy, Y)-> !fas.add((Forall) Fy), null, null);
		ros.add(roImply);
		ros.add(roForall);
		ros.add(roImply);
		result = bfp.reduceByOperands(ros, false);
		if (result != null) return result;
		
		ros.clear();
		fas.clear(); fas.add(b);
		/*
		 * (Fx(C -> (A && D)) && B) && A 
		 * = Fx(C -> (A && D)) && B		...given A depends on ONLY x as Fx
		 * 
		 * (Fx(C -> (Fy(A') && D)) && B) && Fy(A')	...given A is forall
		 * = (Fx(C -> (A'y1 && A'y2 &&...&& A'ym && D)) && B) && A'y1 && A'y2 &&...&& A'ym
		 * = ignoresDependency
		 */
		final ReductionOctet roAnd = new ReductionOctet(
				"(Fx(C -> (A && D)) && B) && A = Fx(C -> (A && D)) && B		...given A depends on ONLY x as Fx\n" + 
				"(Fx(C -> (Fy(A') && D)) && B) && Fy(A') = ignoresDependency	...given A is forall", 
				Operator.And, (Cconsq, d)-> d.equals(p2), null, 
				(Cconsq, newD) -> p2.dependsOnTheSame(b) ? this : ignoreDependency(Operator.And, p2));
		ros.add(roImply);
		ros.add(roAnd);
		/*
		 * (B && Fx(C -> (Fy(E -> A) && D))) && A
		 * = (B && Fx(~C || (Fy(~E || A) && D))) && Exy(A)	...given A depends on ONLY x and y as Fxy
		 * = (B && Fx(~C || (Fy(~E || A) && D))) && (Ax1y1 || Ax1y2 ||...|| Axnym)
		 * = ignoresDependency
		 */
		ros.add(roForall);
		ros.add(roImply);
		result = bfp.reduceByOperands(ros, false);
		if (result != null) return result;
		
		ros.clear();
		fas.clear(); fas.add(b);
		ros.add(roImply);
		ros.add(roAnd);
		ros.add(roForall);
		/*
		 * (Fx(C -> (Fy((F -> A) && E) && D)) && B) && A
		 * = (Fx(~C || (Fy((~F || A) && E) && D)) && B) && Exy(A)	...given A depends on ONLY x and y as Fxy
		 * = ignoresDependency
		 */
		ros.add("(Fx(C -> (Fy((F -> A) && E) && D)) && B) && A = ignoresDependency\n" +
				"...given A depends on ONLY x and y as Fxy", 
				Operator.And, null, null, null);
		ros.add(roImply);
		return bfp.reduceByOperands(ros, false);
	}
	
	private Proposition andByReduceForall2(Proposition p2, Proposition fap, List<Forall> fas) {
		/*
		 * (B /\ Fx(Fy(A /\ C))) /\ A
		 * = (B /\ Fx(Fy(A) /\ Fy(C))) /\ A
		 * = B /\ Fxy(A) /\ Fxy(C) /\ Exy(A)...given A depends on ONLY x and y
		 * = B /\ Fxy(A) /\ Fxy(C) 			...Fx(A) /\ Ex(A) = Fx(A)
		 * = this
		 */
		final ReductionOperations ros = new ReductionOperations();
		ros.add("(B && Fx(Fy(A && C))) && A = this", 
				Predicate.Operator.Forall, null, null, 
				(Fx, Y) -> {Forall fax = (Forall) Fx; 
				return andByReduceForallAnd(
						p2, fax.getProposition(), (List<Forall>) add(fas, fax));});
		return fap.reduceByOperands(ros, false);
	}
	
	private Proposition andByReduceForallAnd(Proposition p2, Proposition fap, List<Forall> fas) {
		final ReductionOperations ros = new ReductionOperations();
		final ReductionOctet andDepX = new ReductionOctet(
				"(B && Fx(C && A)) && A = this				...given A depends on ONLY x as Fx",
				Operator.And, (X, c)-> c.equals(p2), null, (X, newC) -> p2.dependsOnTheSame(fas) ? this : null),
		andIndepX = new ReductionOctet(
				"(B && Fx(C && A)) && A = (B && Fx(C)) && A	...given A in-depends on x",
				Operator.And, (X, c)-> c.equals(p2), null, (X, newC) -> p2.independsOn(fas) ? And.from(newC) : null);
		
		ros.addPrimDisj(andDepX, andIndepX);
//			faiConsq = ((Imply) c).consequent;
//			// (B && Fx[(D -> [E && A]) && C]) && A = ignoresDependency
//			if (faiConsq.getOp() == Operator.And) {
//				for (Proposition e : ((And) faiConsq).getPropositions()) 
//					if (e.equals(p2)) {ignoreDependency(); break;}
//			}
		ros.add("(B && Fx((D -> A) && C)) && A 			= ignoresDependency	...given A depends on ONLY x as Fx\n" + 
				"(B && Fx((D -> (E && A)) && C)) && A 	= ignoresDependency", 
				Operator.Imply, (c, da)-> ((Imply) c).consequent.equals(p2), null, 
				(c, da)-> ((Imply) c).consequent, 
				(c, newDA) -> p2.dependsOnTheSame(fas) ? ignoreDependency(Operator.And, p2) : null);
		ros.add(Operator.And, (cic, e)-> e.equals(p2), null, 
				(cic, E) -> p2.dependsOnTheSame(fas) ? ignoreDependency(Operator.And, p2) : null);
		Proposition result = fap.reduceByOperands(ros, false);
		if (result != null) return result;
		
//			Proposition faiAntec = ((Imply) c).antecedent;
//			// (B && Fx[([E && (F -> [A && G])] -> D) && C]) && A = ignoresDependency
//			if (faiAntec.getOp() == Operator.And) {
//				E: for (Proposition e : ((And) faiAntec).getPropositions()) 
//					if (e.getOp() == Operator.Imply) {
//						faiConsq = ((Imply) e).consequent;
//						if (faiConsq.getOp() == Operator.And) 
//							for (Proposition g : ((And) faiConsq).getPropositions()) 
//								if (g.equals(p2)) {ignoreDependency(); break E;}
//					}
//			}
		ros.clear();
		ros.add(andDepX);
		ros.add("(B && Fx[([E && (F -> [A && G])] -> D) && C]) && A = ignoresDependency", 
				Operator.Imply, null, null, (c, ed)-> ((Imply) c).antecedent, null);
		ros.add(Operator.And, null, null, null);
		ros.add(Operator.Imply, null, null, (e, fg)-> ((Imply) e).consequent, null);
		ros.add(Operator.And, (eic, g)-> g.equals(p2), null, 
				(eic, newG) -> {ignoreDependency(Operator.And, p2); return null;});
		return fap.reduceByOperands(ros, false);
	}
	

	
	/**
	 * (B /\ A) \/ A	...	A	B	A/\B |	(A/\B)\/A
	 * = A					0	0	0	 |	0
	 * 						0	1	0	 |	0
	 * 						1	0	0	 |	1
	 * 						1	1	1	 |	1
	 * 
	 * ((A \/ C) /\ B) \/ A
	 * = (A \/ C \/ A) /\ (B \/ A)
	 * = (A \/ C) /\ (B \/ A)
	 * = (C /\ B) \/ A
	 * 
	 * ((C \/ (A /\ D)) /\ B) \/ A
	 * = ((C \/ A) /\ (C \/ D) /\ B) \/ A
	 * = (C \/ A \/ A) /\ (C \/ D \/ A) /\ (B \/ A)
	 * = (C \/ A) /\ (C \/ D \/ A) /\ (B \/ A)
	 * = (C /\ (C \/ D) /\ B) \/ A
	 * = (C /\ B) \/ A
	 * 
	 * ((((A \/ E) /\ D) \/ C) /\ B) \/ A
	 * = (((A \/ E) /\ D) \/ C \/ A) /\ (B \/ A)
	 * = (A \/ E \/ C \/ A) /\ (D \/ C \/ A) /\ (B \/ A)
	 * = (E \/ C \/ A) /\ (D \/ C \/ A) /\ (B \/ A)
	 * = ((E \/ C) /\ (D \/ C) /\ B) \/ A
	 * = (((E /\ D) \/ C) /\ B) \/ A
	 * 
	 * @see ompca.vodcg.condition.Proposition#orByReduce(ompca.vodcg.condition.Proposition)
	 */
	protected Proposition orByReduce(Proposition p2) {
		if (p2 == null) throwNullArgumentException("p2");
		
		final ReductionOperations ros = new ReductionOperations();
		ros.addPrimDisj(new ReductionOctet( 
				Operator.And, null, null, (p1, newB)-> from(newB).or(()-> p2)),
				new ReductionOctet("(A && B) || A = A", 
				Operator.And, (this_, b)-> b.equals(p2), null, (p1, newB)-> p2),
				new ReductionOctet("(A && B) || (A && C) = A && (B || C)", 
				Operator.And, (this_, b)-> p2.getOp().equals(Operator.And), null, (this_, newB)-> orByReduce(newB, p2.getPropositions())));
		ros.add("((A || C) && B) || A = (C && B) || A", 
				Operator.Or, (b, c)-> c.equals(p2), null, (b, newC)-> Or.from(newC));
		ros.add("(((A && D) || C) && B) || A = (C && B) || A", 
				Operator.And, (c, d)-> d.equals(p2), null, (c, newD)-> ros.isReduced(2) ? null : from(newD));
		ros.add("((((A || E) && D) || C) && B) || A	= (((E && D) || C) && B) || A", 
				Operator.Or, (d, e)-> e.equals(p2), null, (d, newE)-> Or.from(newE));
		Proposition result = reduceByOperands(ros, false);
		if (result != null) return result;

		return super.orByReduce(p2);
	}

	/**
	 * (A && B) || (A && C) = A && (B || C)
	 * 
	 * @param p1s
	 * @param p2s
	 * @return
	 */
	private Proposition orByReduce(Iterable<Proposition> p1s, Iterable<Proposition> p2s) {
		assert p1s != null && p2s != null;

		final List<Proposition> A = new ArrayList<>(), B = new ArrayList<>(), C = new ArrayList<>();
		for (Proposition b : p1s) for (Proposition c : p2s) {
			if (b.equals(c)) A.add(b);
			else {B.add(b); C.add(c);}	// many b/c's are allowed to be reduced
		}
		return A.isEmpty() 
				? null
				: from(A).and(()-> from(B).or(()-> from(C)));
	}
	
	
	
	/**
	 * A factory delegate method to ensure both antecedent and consequent are optimized.
	 * 
	 * (B /\ A) -> B
	 * = ~(A /\ B) \/ B
	 * = ~A \/ ~B \/ B
	 * = ~A \/ T
	 * = T
	 * 
	 * (B /\ ~(A /\ C)) -> A
	 * = ~(~(A /\ C) /\ B) \/ A
	 * = (A /\ C) \/ ~B \/ A
	 * = ~B \/ A
	 * = B -> A
	 * 
	 * (B /\ (A \/ C)) -> A
	 * = ~((A \/ C) /\ B) \/ A
	 * = ~(A \/ C) \/ ~B \/ A
	 * = (~A /\ ~C) \/ ~B \/ A
	 * = (~A \/ ~B \/ A) /\ (~C \/ ~B \/ A)
	 * = ~C \/ ~B \/ A
	 * = ~(C /\ B) \/ A
	 * = (C /\ B) -> A
	 * 
	 * (B /\ (A /\ C)) -> A
	 * = ~(B /\ A /\ C) \/ A
	 * = ~B \/ ~A \/ ~C \/ A
	 * = ~B \/ ~C
	 * = ~(B /\ C)
	 * 
	 * (B /\ (C /\ (D -> A))) -> A
	 * = ~(B /\ (C /\ (~D \/ A))) \/ A
	 * = ~B \/ ~(C /\ (~D \/ A)) \/ A
	 * = ~B \/ ~C \/ ~(~D \/ A) \/ A
	 * = ~B \/ ~C \/ (D /\ ~A) \/ A
	 * = ~B \/ ~C \/ ((D \/ A) /\ (~A \/ A))
	 * = ~B \/ ~C \/ D \/ A
	 * = ~(B /\ C) \/ D \/ A
	 * = (B /\ C) -> (D \/ A)
	 * 
	 * (B /\ (C -> A)) -> A
	 * = ~((~C \/ A) /\ B) \/ A
	 * = ~(~C \/ A) \/ ~B \/ A
	 * = (C /\ ~A) \/ ~B \/ A
	 * = (C \/ ~B \/ A) /\ (~A \/ ~B \/ A)
	 * = C \/ ~B \/ A
	 * = B -> (C \/ A)
	 * 
	 * (a1<=x<=a2 /\ D) -> (B /\ Forall x a1<=x<=a2 -> C(x))
	 * = (a1<=x<=a2 /\ D) -> (B /\ (a1<=x1<=a2 -> C(x1)) /\ ... /\ (a1<=a1<=a2 -> C(a1)) /\ ... /\ (a1<=a2<=a2 -> C(a2)) /\ ... /\ (a1<=xn<=a2 -> C(xn)))
	 * = (a1<=x<=a2 /\ D) -> (B /\ T /\ ... /\ C(a1) /\ ... /\ C(a2) /\ ... /\ T)
	 * = (a1<=x<=a2 /\ D) -> (B /\ C(a1) /\ ... /\ C(a2))		Y:
	 * 														A D Fx(A->B)| ~A Ex(A/\~B) ~D ~D\/Y formula
	 * (A /\ D) -> Forall x A(x) -> B(x)					0 0	0		| 1		1		1	-	-
	 * = ~(A /\ D) \/ Fx(A->B)								0 0	1		| 1		0		1	1	1
	 * = ~A \/ ~D \/ Fx(A->B)								0 1	0		| 1		1		0	-	-
	 * 	...when the goal is to make A/Fx(A->B) a singleton	0 1	1		| 1		0		0	1	1
	 * = ~D \/ Fx(A->B)										1 0	0		| 0		1		1	1	1
	 * = D -> Fx(A->B)										1 0	1		| 0		0		1	1	1
	 * TODO: automatic truth-table building/matching for 	1 1	0		| 0		1		0	0	0
	 * 	ALL possible singleton relation combinations		1 1	1		| 0		0		0	1	1
	 * 																			D->
	 * (A /\ D) -> (B /\ Forall x A(x) -> C(x))					A D Fa 	formula	B/\Fa
	 * = (Exists x A(x) /\ D) -> (B /\ Forall x A(x) -> C(x))	0 0  0	-		-
	 * 		[(~Forall x A(x) -> C(x)) -> Forall x A(x)			0 0  1	1		1 
	 * 		-> Exists x A(x)]									0 1  0	-		-
	 * 		[~A -> ~Exists x A(x) -> Forall x ~A(x)]			0 1  1	1		B
	 * = (~A /\ D /\ Fa) \/ (D -> (B /\ Fa))					1 0  0	1		1
	 * = (~A /\ D /\ Fa) \/ ~D \/ (B /\ Fa)						1 0  1	1		1
	 * = ((~A \/ ~D) /\ (Fa \/ ~D)) \/ (B /\ Fa)				1 1  0	0		0
	 * = (~A /\ Fa) \/ ~D \/ (B /\ Fa)							1 1  1	B		B
	 * = (~A /\ Fa) \/ (B /\ Fa) \/ ~D							
	 * = ((~A \/ B) /\ Fa) \/ ~D
	 * = D -> ((A -> B) /\ Fa)													D->
	 * 															A Fa 	formula	B/\Fa
	 * 															0 0		-		-
	 * 															0 1		1		D->B
	 * 															1 0		D->F	D->F
	 * 															1 1		D->B	D->B
	 * 
	 * 		...when the goal is to make A/Fa(A->C) a singleton			
	 * 																	(A->B)	formula
	 * 															B C D	/\Fa	D->((A->B)/\Fa)
	 * 															0 0 0	~A/\Fa	1
	 * 															0 0 1	~A/\Fa	~A/\Fa
	 * 															0 1 0	~A/\Fa	1
	 * 															0 1 1	~A/\Fa	~A/\Fa
	 * 															1 0 0	Fa		1
	 * 															1 0 1	Fa		Fa
	 * 															1 1 0	Fa		1
	 * 															1 1 1	Fa		Fa
	 * = ~D \/ (~B /\ D /\ (~A /\ Fa(A->C))) \/ (B /\ D /\ Fa(A->C))
	 * = ~D \/ (~B /\ D /\ (Ex(~A) /\ Fa(A->C))) \/ (B /\ D /\ Fa(A->C))
	 * = ~D \/ (~B /\ D /\ (~Fa(A) /\ Fa(~A\/C))) \/ (B /\ D /\ Fa(~A\/C))
	 * = ~D \/ (~B /\ D /\ ~(A1/\A2/\.../\An) /\ ~A1\/C1 /\ ~A2\/C2 /\.../\ ~An\/Cn) \/ (B /\ D /\ Fa(~A\/C))
	 * 						...	~(A1/\A2/\A3) /\ A1->C1 /\ A2->C2 /\ A3->C3 ...(1)
	 * 							= (~A1\/~A2\/~A3) /\ ~A1\/C1 /\ ~A2\/C2 /\ ~A3\/C3	~A1	~A2	~A3	(1)
	 * 																				0	0	0	0
	 * 																				0	0	1	C1/\C2
	 * 																				0	1	0	C1/\C3
	 * 																				0	1	1	C1
	 * 																				1	0	0	C2/\C3
	 * 																				1	0	1	C2
	 * 																				1	1	0	C3
	 * 																				1	1	1	1
	 * 							= 	((~A1 /\ ~A1\/C1) \/ 
	 * 								(~A2 /\ ~A1\/C1) \/ 
	 * 								(~A3 /\ ~A1\/C1)) /\ ~A2\/C2 /\ ~A3\/C3
	 * 							= 	((~A1 /\ ~A1)\/(~A1 /\ C1) \/ 
	 * 								(~A2 /\ ~A1)\/(~A2 /\ C1) \/ 
	 * 								(~A3 /\ ~A1)\/(~A3 /\ C1)) /\ ~A2\/C2 /\ ~A3\/C3
	 * 							= (~A1 \/ (~A1 /\ C1) \/ (~A2 /\ ~A1) \/ (~A2 /\ C1) \/ (~A3 /\ ~A1) \/ (~A3 /\ C1)) /\ ~A2\/C2 /\ ~A3\/C3
	 * 							= ((~A1 /\ ~A2\/C2) \/ (~A1 /\ C1 /\ ~A2\/C2) \/ (~A2 /\ ~A1 /\ ~A2\/C2) \/ (~A2 /\ C1 /\ ~A2\/C2) \/ (~A3 /\ ~A1 /\ ~A2\/C2) \/ (~A3 /\ C1 /\ ~A2\/C2)) /\ ~A3\/C3
	 * 							= ((~A1 /\ ~A2\/C2) \/ (~A1 /\ C1 /\ ~A2\/C2) \/ (~A2 /\ ~A1) \/ (~A2 /\ C1) \/ (~A3 /\ ~A1 /\ ~A2\/C2) \/ (~A3 /\ C1 /\ ~A2\/C2)) /\ ~A3\/C3
	 * 							= (~A1 /\ ~A2\/C2 /\ ~A3\/C3) \/ (~A1 /\ C1 /\ ~A2\/C2 /\ ~A3\/C3) \/ (~A2 /\ ~A1 /\ ~A3\/C3) \/ (~A2 /\ C1 /\ ~A3\/C3) \/ (~A3 /\ ~A1 /\ ~A2\/C2) \/ (~A3 /\ C1 /\ ~A2\/C2)
	 * 							= (~A1 /\ ~(A2/\~C2) /\ ~(A3/\~C3)) \/ (~A1 /\ C1 /\ ~(A2/\~C2) /\ ~(A3/\~C3)) \/ (~A2 /\ ~A1 /\ ~(A3/\~C3)) \/ (~A2 /\ C1 /\ ~(A3/\~C3)) \/ (~A3 /\ ~A1 /\ ~(A2/\~C2)) \/ (~A3 /\ C1 /\ ~(A2/\~C2))
	 * 							= 	~(A1 \/ (A2/\~C2) \/ (A3/\~C3)) /\ 
	 * 								~(A1 \/ ~C1 \/ (A2/\~C2) \/ (A3/\~C3)) /\ 
	 * 								~(A2 \/ A1 \/ (A3/\~C3)) /\ 
	 * 								~(A2 \/ ~C1 \/ (A3/\~C3)) /\ 
	 * 								~(A3 \/ A1 \/ (A2/\~C2)) /\ 
	 * 								~(A3 \/ ~C1 \/ (A2/\~C2))
	 * 						...	~(A1/\A2/\.../\An) /\ A1->C1 /\ A2->C2 /\.../\ An->Cn
	 * 							... ~(An->Cn) -> An
	 * = ~D \/ (~B /\ D /\ (~A1\/~A2\/...\/~An) /\ ~A1\/C1 /\ ~A2\/C2 /\.../\ ~An\/Cn) \/ (B /\ D /\ Fa(~A\/C))
	 * 																Fa	Fa	Fa(A)	Fa	  Fa(A)		Fa
	 * 						...A1 A2 ... An-1 An C1 C2 ... Cn-1 Cn (A) (C) /\Fa(C) (A/\C) \/Fa(C) (A\/C)
	 * 							0  0  ...	0  0  0  0 ...	0	0	0	0		0	0		0		0
	 * 													...
	 * 							0  0  ...	0  0  1  1 ...	1	1	0	1		0	0		1		1
	 * 							0  ??0  ...	0	  1	  0  0 ...	0  0		1		0		0
	 * 													...
	 * 							0	0  ...	0	  1	  1  1 ...	1  0		1		1		1
	 * 							0	0  ...	1	  0	  0  0 ...	0  0		1		0		0
	 * 													...
	 * 
	 * 																	(A->B)	formula
	 * = (~Fa /\ ~D) \/ (~B /\ Fa /\ (D -> ~A)) \/ (B /\ Fa)	B Fa	/\Fa	D->((A->B)/\Fa)
	 * 															0 0		0		~D
	 * 															0 1		~A		D->~A
	 * 															1 0		0		~D
	 * 															1 1		1		1
	 * 
	 * 		or																	D->		 
	 * = (~B /\ D /\ Fa(A->C) /\ ~A) \/ (D -> (B /\ Fa(A->C)))	B D Fa 	formula	B/\Fa	~D\/B\/Fa
	 * 															0 0 0	1		1		1
	 * 															0 0 1	1		1		1
	 * 															0 1 0	0		0		0
	 * 															0 1 1	~A		0		1
	 * 															1 0 0	1		1		1
	 * 															1 0 1	1		1		1
	 * 															1 1 0	0		0		0
	 * 															1 1 1	1		1		1
	 * 
	 * = (~B /\ D /\ Fa(A->C) /\ Ex(~A)) \/ (~D \/ (B /\ Fa(A->C)))
	 * = (D /\ ~B /\ Fa(A->C) /\ ~Fa(A)) \/ ~D \/ (B /\ Fa(A->C))
	 * = ((~B \/ ~D) /\ (Fa(A->C) \/ ~D) /\ (~Fa(A) \/ ~D)) \/ (B /\ Fa(A->C))
	 * = (((~B \/ ~D) /\ (Fa(A->C) \/ ~D) /\ (~Fa(A) \/ ~D)) \/ B) /\ (((~B \/ ~D) /\ (Fa(A->C) \/ ~D) /\ (~Fa(A) \/ ~D)) \/ Fa(A->C))
	 * = (Fa(A->C) \/ ~D \/ B) /\ (~Fa(A) \/ ~D \/ B) /\ (~B \/ ~D \/ Fa(A->C)) /\ (Fa(A->C) \/ ~D) /\ (~Fa(A) \/ ~D \/ Fa(A->C))
	 * = (Fa(A->C) \/ ((~D \/ B) /\ (~B \/ ~D) /\ ~D /\ (~Fa(A) \/ ~D))) /\ (~Fa(A) \/ ~D \/ B)
	 * = (Fa(A->C) \/ ~D) /\ (~Fa(A) \/ ~D \/ B)
	 * = (Fa(A->C) /\ (~Fa(A) \/ B)) \/ ~D
	 * 															B D Fa(A) Fa(A->C)	formula
	 * 															0 0		0		0		-
	 * 															0 0		0		1		1
	 * 															0 0		1		0		1
	 * 															0 0		1		1		1
	 * 															0 1		0		0		-
	 * 															0 1		0		1		1
	 * 															0 1		1		0		0
	 * 															0 1		1		1		0
	 * 															1 0		0		0		-
	 * 															1 0		0		1		1
	 * 															1 0		1		0		1
	 * 															1 0		1		1		1
	 * 															1 1		0		0		-
	 * 															1 1		0		1		1
	 * 															1 1		1		0		0
	 * 															1 1		1		1		1
	 * 		
	 * = ~D \/ ((~A1 \/ ~A2 \/ ... \/ ~An \/ B) /\ ~A1\/C1 /\ ~A2\/C2 /\ ... /\ ~An\/Cn)
	 * 				...	~/\An	B 	~/\An \/ B	(~/\An \/ B) /\ /\(An->Cn)
	 * 						0	0		0			0
	 * 						0	1		1			1
	 * 						1	0		1			/\(An->Cn)
	 * 						1	1		1			/\(An->Cn)
	 * = ~D \/ (Fa(A) /\ B) \/ (~Fa(A) /\ Fa(A->C))
	 * = ~D \/ (((Fa(A) /\ B) \/ ~Fa(A)) /\ ((Fa(A) /\ B) \/ Fa(A->C)))
	 * = ~D \/ ((B \/ ~Fa(A)) /\ (Fa(A) \/ Fa(A->C)) /\ (B \/ Fa(A->C)))	
	 * ??
	 * = ~D \/ (((~A1 /\ ~A2 /\ ... /\ ~An) /\ (~A1\/C1 /\ ~A2\/C2 /\ ... /\ ~An\/Cn)) \/ (B /\ (~A1\/C1 /\ ~A2\/C2 /\ ... /\ ~An\/Cn)))
	 * 			...X /\ Y /\ (X \/ Z) = (X /\ Y) \/ (X /\ Y /\ Z) = X /\ Y
	 * = ~D \/ ((~A1 /\ ~A2 /\ ... /\ ~An) \/ (B /\ (~A1\/C1 /\ ~A2\/C2 /\ ... /\ ~An\/Cn)))
	 * = ~D \/ (((~A1 /\ ~A2 /\ ... /\ ~An) \/ B) /\ ((~A1 /\ ~A2 /\ ... /\ ~An) \/ (~A1\/C1 /\ ~A2\/C2 /\ ... /\ ~An\/Cn)))
	 * 													...(X /\ Y) \/ X \/ Z = X \/ Z
	 * = ~D \/ (~A1\/B /\ ~A2\/B /\ ... /\ ~An\/B /\ ~A1\/C1 /\ ~A2\/C2 /\ ... /\ ~An\/Cn)
	 * = ~D \/ (~A1\/(B/\C1) /\ ~A2\/(B/\C2) /\ ... /\ ~An\/(B/\Cn))
	 * = D -> Fa(A -> (B/\C))	...given B is independent on x
	 * 
	 * 		or
	 * = ~D \/ ((~A1 \/ ~A2 \/ ... \/ ~An \/ B) /\ (~A1\/C1 /\ ~A2\/C2 /\ ... /\ ~An\/Cn))
	 * 
	 * 		or
	 * = (~Fa(~A) /\ D) -> (~Fa(~B) /\ Fa(A->C))			
	 * = ~(~Fa(~A) /\ D) \/ (~Fa(~B) /\ Fa(A->C))			X:Fa Y:Fa Z:Fa	 X\/	 Fa(~A\/
	 * = ~D \/ Fa(~A) \/ (~Fa(~B) /\ Fa(~A\/C))				(~A) (~B) (A->C) (~Y/\Z) (~B/\(A->C)))
	 * 														0	 0	  0			-		-
	 * 														0	 0	  1			1		1
	 * 														0	 1	  0			0		0
	 * 														0	 1	  1			0		1
	 * 														1	 0	  0			-		??
	 * 														1	 0	  1			1
	 * 														1	 1	  0			1
	 * 														1	 1	  1			1
	 * = ~D \/ ((Fa(~A) \/ ~Fa(~B)) /\ (Fa(~A) \/ Fa(~A\/C)))
	 * = ~D \/ (((~A1 /\ ~A2 /\ ... /\ ~An) \/ ~(~B1 /\ ~B2 /\ ... /\ ~Bn)) /\ ((~A1 /\ ~A2 /\ ... /\ ~An) \/ (~A1\/C1 /\ ~A2\/C2 /\ ... /\ ~An\/Cn))
	 * = ~D \/ (((~A1 /\ ~A2 /\ ... /\ ~An) \/ ~(~B1 /\ ~B2 /\ ... /\ ~Bn)) /\ (~A1\/C1 /\ ~A2\/C2 /\ ... /\ ~An\/Cn))
	 * 																			...(X /\ Y) \/ X \/ Z = X \/ Z
	 * = ~D \/ ((~A1 /\ ~A2 /\ ... /\ ~An /\ ~A1\/C1 /\ ~A2\/C2 /\ ... /\ ~An\/Cn) \/ (~(~B1 /\ ~B2 /\ ... /\ ~Bn) /\ (~A1\/C1 /\ ~A2\/C2 /\ ... /\ ~An\/Cn)))
	 * = ~D \/ ((~A1 /\ ~A2 /\ ... /\ ~An) \/ (~(~B1 /\ ~B2 /\ ... /\ ~Bn) /\ (~A1\/C1 /\ ~A2\/C2 /\ ... /\ ~An\/Cn)))
	 * 			...X /\ (X \/ Y) = X
	 * = ~D \/ ((~A1 /\ ~A2 /\ ... /\ ~An) \/ ((B1 \/ B2 \/ ... \/ Bn) /\ ~A1\/C1 /\ ~A2\/C2 /\ ... /\ ~An\/Cn))
	 * 											...??~/\X /\ (Y \/ Z) = /\~X...
	 * ??
	 * = (Fa(~A) \/ ~D \/ ~Fa(~B)) /\ (Fa(~A) \/ ~D \/ Fa(~A\/C))
	 * = (Fa(~A) \/ ~D \/ ~Fa(~B)) /\ (~D \/ (~A1 /\ ~A2 /\ ... /\ ~An) \/ (~A1\/C1 /\ ~A2\/C2 /\ ... /\ ~An\/Cn))
	 * = (Fa(~A) \/ ~D \/ ~Fa(~B)) /\ (~D \/ (~A1\/C1 /\ ~A2\/C2 /\ ... /\ ~An\/Cn))
	 * 						...(X /\ Y) \/ X \/ Z = X \/ Z
	 * = ((~A1 /\ ~A2 /\ ... /\ ~An) \/ ~D \/ ~(~B1 /\ ~B2 /\ ... /\ ~Bn)) /\ (~D \/ (~A1\/C1 /\ ~A2\/C2 /\ ... /\ ~An\/Cn))
	 * = ((~A1 /\ ~A2 /\ ... /\ ~An) \/ ~D \/ B1 \/ B2 \/ ... \/ Bn)) /\ (~D \/ (~A1\/C1 /\ ~A2\/C2 /\ ... /\ ~An\/Cn))
	 * ??
	 * 
	 * @param consq
	 * @return
	 */
	@SuppressWarnings("unchecked")
	protected Proposition implyByReduce(final Proposition consq) {
		if (consq == null) throwNullArgumentException("consequence");
		
		if (contains(consq)) return True.from("(B && A) -> B = T", Operator.Imply, this, consq);
		
		final ReductionOctet newBimplyConsq = new ReductionOctet(
				Operator.And, null, null, (this_, newB)-> from(newB).imply(()-> consq));
		final ReductionOperations ros = new ReductionOperations();
		
		ros.add(newBimplyConsq);	
		ros.add("(~(A && C) && B) -> A = B -> A", 
				Operator.Not, null, null, null);	
		ros.add(Operator.And, (bn, c)-> c.equals(consq), null, (bn, newC)-> null);	
		Proposition result = reduceByOperands(ros, false);
		if (result != null) return result;
		
		ros.clear();
		ros.add(newBimplyConsq);	
		ros.add("((A || C) && B) -> A = (C && B) -> A", 
				Operator.Or, (b, c)-> c.equals(consq), null, (b, newC)-> Or.from(newC));	
		result = reduceByOperands(ros, false);
		if (result != null) return result;
		
		ros.clear();
		ros.add("(B && (A && C)) -> A = ~(B && C)", 
				Operator.And, null, null, (this_, newB)-> from(newB).not());	
		ros.add(Operator.And, (b, c)-> c.equals(consq), null, (b, newC)-> from(newC));	
		result = reduceByOperands(ros, false);
		if (result != null) return result;
		
		final ReductionOctet newBimplyOr = new ReductionOctet(
				Operator.And, null, null, (this_, newB)-> from(newB).imply(()-> ros.getResult(0,0))),
				or = new ReductionOctet("((C -> A) && B) -> A = B -> (C || A)", 
				Operator.Imply, (b, c)-> ((Imply) b).consequent.equals(consq), null, 
				(b, newB)-> {ros.setReduced(0, 0, ((Imply) b).antecedent.or(()-> consq)); return null;});
		ros.clear();
		ros.add(newBimplyOr);	
		ros.add(or);	
		result = reduceByOperands(ros, false);
		if (result != null) return result;
		
		ros.clear();
		ros.add(newBimplyOr);	
		ros.add("(B && (C && (D -> A))) -> A = (B && C) -> (D || A)", 
				Operator.And, null, null, (b, newC)-> from(newC));	
		ros.add(or);	
		result = reduceByOperands(ros, false);
		if (result != null) return result;
		
		final Relation.Operator consqOp = consq.getOp();
		if (consqOp == Operator.And) {
			ros.clear();
			ros.add("(A && B) -> (C && Fx(A -> D)) = B -> Fx(A -> (C && D))	...given C is independent on x", 
					Operator.And, (this_, b)-> {ros.setTemp("b",b); return false;}, null,
					(this_, b)-> consq, (this_, newB)-> from(newB).imply(()-> 
					Forall.from((Set<VariablePlaceholder<?>>) ros.getTemp("qs"), 
							((Proposition) ros.getTemp("b")).imply(()-> ros.getTemp("C && D")))));
			ros.add(Operator.And, null, null, (consq_, newC)-> {ros.setTemp("C && D", from(newC)); return null;});
			ros.add(Predicate.Operator.Forall, (c, X)-> {ros.setTemp("qs", ((Forall) c).getQuantifiers()); return false;}, 
					null, (c, newX)-> newX.get(0));												// return D
			ros.add(Operator.Imply, (X, ad)-> ((Imply) X).antecedent.equals(ros.getTemp("b")), 
					(X, ad)-> ad, (X, newAD)-> newAD.get(1));									// return D
			result = reduceByOperands(ros, false);
			if (result != null) return result;
			
			for (Proposition b : getPropositions()) {
				final Proposition result_ = implyByReduce((And) consq, b);
				if (result_ != null) return imply(()-> result_);
				
				// TODO: (a1<=x<=a2 /\ D) -> (B /\ Forall x a1<=x<=a2 -> C(x))
				// = (a1<=x<=a2 /\ D) -> (B /\ C(a1) /\ ... /\ C(a2))
			}
		}
		
		if (consqOp == Predicate.Operator.Forall) {
			Expression bfp = ((Forall) consq).getFirstOperand();
			if (bfp instanceof Imply) {
				boolean isReduced = false;
				List<Proposition> Ds = new ArrayList<>();
				for (Proposition d : getPropositions()) {
					// (A /\ D) -> Forall x A(x) -> B(x) = D -> Fx(A->B)
					if (((Imply) bfp).antecedent.equals(d)) isReduced = true;
					else Ds.add(d);
				}
				// doing the rest optimization if not isReduced
				if (isReduced) return from(Ds).imply(()-> consq);
			}
		}
		return super.implyByReduce(consq);
	}
	
	/**
	 * A factory delegate method to ensure both antecedent and consequent are optimized.
	 * For separated and precise And-type Proposition/Predicate handling.
	 * 
	 * (A /\ D) -> (B /\ (C -> A))
	 * = ~(A /\ D) \/ (B /\ (~C \/ A))
	 * = ~A \/ ~D \/ (B /\ ~C) \/ (B /\ A)
	 * = ~D \/ (B /\ ~C) \/ ((~A \/ B) /\ (~A \/ A))
	 * = ~D \/ (B /\ ~C) \/ ~A \/ B
	 * = ~D \/ ~A \/ B
	 * = (A /\ D) -> B
	 * 
	 * (A /\ D) -> (B /\ (A -> C))
	 * = ~(A /\ D) \/ (B /\ (~A \/ C))
	 * = ~A \/ ~D \/ (B /\ ~A) \/ (B /\ C)
	 * = ~A \/ ~D \/ (B /\ C)
	 * = (A /\ D) -> (B /\ C)
	 * 
	 * (A /\ D) -> (B /\ ((E /\ A) -> C))
	 * = ~(A /\ D) \/ (B /\ (~(E /\ A) \/ C))
	 * = ~A \/ ~D \/ (B /\ (~E \/ ~A \/ C))
	 * = ~A \/ ~D \/ (B /\ ~E) \/ (B /\ ~A) \/ (B /\ C)
	 * = ~A \/ ~D \/ (B /\ ~E) \/ (B /\ C)
	 * = (A /\ D) -> (B /\ (E -> C))
	 * 
	 * (A /\ D) -> (B /\ (C -> (E /\ (A -> F))))
	 * = ~(A /\ D) \/ (B /\ (~C \/ (E /\ (~A \/ F))))
	 * = ~A \/ ~D \/ (B /\ ~C) \/ (B /\ E /\ ~A) \/ (B /\ E /\ F)
	 * = ~A \/ ~D \/ (B /\ ~C) \/ (B /\ E /\ F)
	 * = ~(A /\ D) \/ (B /\ (~C \/ (E /\ F)))
	 * = (A /\ D) -> (B /\ (C -> (E /\ F)))
	 * 
	 * @param consq
	 * @param b
	 * @return
	 * @throws Exception 
	 */
	private Proposition implyByReduce(final And consq, final Proposition b) {
		final ReductionOperations ros = new ReductionOperations();
		final ReductionOctet implyAnd = new ReductionOctet(
				Operator.And, null, null, (consq_, newC)-> from(newC));
		ros.add(implyAnd);	
		ros.add("(A && B) -> (C && (A -> D)) = (A && B) -> (C && D)",
				Operator.Imply, (c, ad)-> ((Imply) c).antecedent.equals(b), 
				(c, ad)-> ad, (c, newAD)-> newAD.get(1));	// return D	
		Proposition result = consq.reduceByOperands(ros, false);
		if (result != null) return result;	// imply(result) at caller;

		ros.clear();
		ros.add(implyAnd);	
		ros.add("(A && B) -> (C && ((E && A) -> D)) = (A && B) -> (C && (E -> D))",
				Operator.Imply, null, null, (c, ed)-> ((Imply) c).antecedent, 
				(c, newED)-> newED.get(0).imply(()-> newED.get(1)));	
		ros.add(Operator.And, (cia, e)-> e.equals(b), null, (cia, newE)-> from(newE));	
		result = consq.reduceByOperands(ros, false);
		if (result != null) return result;	// imply(result) at caller;
		
		ros.clear();
		ros.add(implyAnd);	
		ros.add("(A && B) -> (C && (D -> A)) = (A && B) -> C", 
				Operator.Imply, (c, d)-> (((Imply) c).consequent).equals(b), null, null);	
		result = consq.reduceByOperands(ros, false);
		if (result != null) return result;	// imply(result) at caller;
		
		ros.clear();
		ros.add(implyAnd);	
		ros.add("(A && B) -> (C && (D -> (E && (A -> F)))) = (A && B) -> (C && (D -> (E && F)))", 
				Operator.Imply, null, null, (c, de)-> ((Imply) c).consequent, 
				(c, newDE)-> newDE.get(0).imply(()-> newDE.get(1)));	
		ros.add(Operator.And, null, null, (d, newE)-> from(newE));	
		ros.add(Operator.Imply, (e, af)-> ((Imply) e).antecedent.equals(b), 
				(e, af)-> af, (e, newAF)-> newAF.get(1));	// return F	
		result = consq.reduceByOperands(ros, false);
		if (result != null) return result;	// imply(result) at caller;
		
		/* Ex((A && B) -> (C && Fx(A -> D)))
		 * = Ex(~(A && B) || (C && Fx(~A || D)))
		 * = Ex(~A || ~B || (C && Fx(~A || D)))
		 * = Ex(~A || ~B || C) && Ex(~A || ~B || Fx(~A || D))
		 * = Ex(~A || ~B || C) && (~A1 || ~A2 ||...|| ~An || ~B || ((~A1 || D1) && (~A2 || D2) &&...&&(~An || Dn)))
		 * = Ex(~A || ~B || C) && (~A1 || ~A2 ||...|| ~An || ~B || D1) && (~A1 || ~A2 ||...|| ~An || ~B || D2) 
		 * 		&&...&&(~A1 || ~A2 ||...|| ~An || ~B || Dn)
		 * = Ex(~A || ~B || C) && (~A1 || ~A2 ||...|| ~An || ~B || (D1 && D2 &&...&& Dn))
		 * = (~A || ~B || C) && (~A || ~B || Fx(D))
		 * = ~A || ~B || (C && Fx(D))
		 * = (A && B) -> (C && Fx(D))
		 */
		ros.clear();
		ros.add(implyAnd);	
		ros.add("(A && B) -> (C && Fx(A -> D)) = (A && B) -> (C && Fx(D))", 
				Predicate.Operator.Forall, (c, newX)-> b.dependsOn(((Forall) c).getQuantifiers()), null, 
				(c, newX)-> Forall.from(((Forall) c).getQuantifiers(), newX.get(0)));	
		ros.add(Operator.Imply, (X, ad)-> ((Imply) X).antecedent.equals(b), 
				(X, ad)-> ad, (X, newAD)-> newAD.get(1));	// return D	
		result = consq.reduceByOperands(ros, false);
		if (result != null) return result;	// imply(result) at caller;
		
		return null;
	}
	
	
	
	protected Proposition notByReduce() {
		final List<Proposition> notProps = reduceByDeMorgan();
		return notProps.isEmpty()
				? null
				: Or.from(notProps);
	}

	
	
	public Expression reduceOnce() {
		if (hasOnlyOperand()) return getFirstOperand();
		super.reduceOnce();
		return this;
	}


	
//	protected boolean equalsToCache(Element e2) {
//		if (e2 == null) Debug.throwNullArgumentException("e2");
//		
//		And a2 = (And) e2;
//		// (A && ~A) = (~A && A) 
//		for (Proposition p : getPropositions())
//			for (Proposition p2 : a2.getPropositions())
//				if (p.equals(p2.not())) return false;
//		return super.equalsToCache(e2);
//	}
	
	

//	/**
//	 * An infix serialization.
//	 *  
//	 * @see ompca.vodcg.condition.ConditionElement#toNonEmptyString()
//	 */
//	@Override
//	public String toNonEmptyString() {
//		assert (props != null);
//		
//		String cond = "";
//		Iterator<Proposition> itProps = props.iterator();
//		if (itProps.hasNext()) {
//			cond = "(";
//			do {
//				cond += itProps.next().toString();
//				if (itProps.hasNext()) cond += " /\\ "; 
//				else break;
//			} while (true);
//			cond += ")"; 
//		}
//		return cond;
//	}
	
}