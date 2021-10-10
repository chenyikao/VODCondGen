/**
 * 
 */
package ompca.vodcg.condition;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

/**
 * @author Kao, Chen-yi
 *
 */
public class Or extends Proposition {
	
	final static private Map<Set<Proposition>, Or> OR_CACHE = new HashMap<>();
	
	private Or(Proposition prop) {
		// Operands preparation
		super(Operator.Or, new HashSet<>(), prop.getScopeManager());
//		init();
		add(prop);
	}
	
	/**
	 * @param lhsp
	 * @param rhsp
	 */
	private Or(Proposition lhsp, Proposition rhsp) {
		this(lhsp);	// TODO: lhsp.scope \/ rhsp.scope
		add(rhsp);
	}
	
	/**
	 * @param disjunction - should NOT be empty.
	 * @param scope
	 */
	private Or(Set<Proposition> disjunction) {
		super(	Operator.Or, 
				disjunction, 
				disjunction.iterator().next().getScopeManager());	// TODO: \/ conjunction.scope
//		init();
	}


	
//	@SuppressWarnings("unchecked")
//	private void init() {
//		props = (Set<Proposition>) operands;
//	}
	

	
//	final public static Or get(Proposition p) {
//		if (p == null) return null;
//		if (p instanceof Or) return (Or) p;
//		
//		Set<Proposition> ps = Collections.singleton(p);
//		Or result = (Or) OrCache.get(ps);
//		if (result != null) return result;
//		
//		OrCache.put(ps, result = new Or(p)); 
//		return result;
//	}
	
	/**
	 * Empty/constant propositions may have contradict semantics and their disjunction
	 * result is left to {@link Proposition#orByReduce(Proposition)}.
	 * 
	 * @param p1
	 * @param p2
	 * @return
	 */
	@SuppressWarnings("unchecked")
	final public static Proposition from(Proposition p1, Supplier<Proposition> p2sp) {
		return from(Operator.Or, p1, p2sp, ()-> {
			
			// default hierarchical flattening: Or.orByReduce(Or)
			final Proposition p2 = p2sp.get();
			final boolean p1io = p1.getOp().equals(Operator.Or), p2io = p2.getOp().equals(Operator.Or);
			final Set<Proposition> ps = p1io 		// with set optimization
					? (Set<Proposition>) p1.toSet() 
					: new HashSet<>(Collections.singleton(p1));
			if (p2io) ps.addAll((Set<Proposition>) p2.toSet());
			else ps.add(p2);
			
			Or or = OR_CACHE.get(ps);
			if (or == null) OR_CACHE.put(ps, or = new Or(ps));
			return or;});
//			return p1io && p2io ? get(new ArrayList<>(ps)) : new Or(ps);});
	}
	
	/**
	 * Linearization during optimization saves hashing time.
	 * 
	 * @param disjunction
	 * @return
	 */
	final public static Proposition from(List<? extends Proposition> disjunction) {
		if (disjunction == null || disjunction.isEmpty()) 
			return throwNullArgumentException("Empty Or?");
		if (disjunction.size() == 1) return disjunction.iterator().next(); 

//		Proposition result = OrCache.get(disjunction);
//		if (result != null) return result;
//		Proposition result = null;
		
		Proposition merge = null;
		List<Proposition> mergeDisj = new ArrayList<>();
		// binary merge reduction
		for (Proposition p : disjunction) {
			if (merge == null) merge = p;
			else {mergeDisj.add(from(merge, ()-> p)); merge = null;}
		}
		if (merge != null) mergeDisj.add(merge);
		return from(mergeDisj);

//		for (Proposition p : disjunction) result = result == null ? p : get(result, p);
//		OrCache.put(disjunction, result);
//		return result;
//		return result.clone();
	}
	
	
	
	/**
	 * (B \/ A) /\ A	... A	B	A\/B |	(A\/B)/\A
	 * = A					0	0	0	 |	0
	 * 						0	1	1	 |	0
	 * 						1	0	1	 |	1
	 * 						1	1	1	 |	1
	 * (B \/ ~A) /\ A
	 * = (B /\ A) \/ (~A /\ A)
	 * = B /\ A
	 * 
	 * (B \/ (C /\ A)) /\ A
	 * = (B /\ A) \/ (C /\ A /\ A)
	 * = (B /\ A) \/ (C /\ A)
	 * = (B \/ C) /\ A
	 * 
	 * (B \/ (C /\ (D \/ A))) /\ A
	 * = (B \/ (C /\ D) \/ (C /\ A)) /\ A
	 * = (B /\ A) \/ (C /\ D /\ A) \/ (C /\ A /\ A)
	 * = (B /\ A) \/ (C /\ D /\ A) \/ (C /\ A)
	 * = (B \/ (C /\ D) \/ C) /\ A
	 * = (B \/ C) /\ A
	 * 
	 * (B \/ (C /\ (D \/ (E /\ A)))) /\ A
	 * = (B /\ A) \/ (C /\ A /\ (D \/ (E /\ A)))
	 * = (B /\ A) \/ (C /\ A /\ D) \/ (C /\ A /\ E /\ A)
	 * = (B /\ A) \/ (C /\ A /\ D) \/ (C /\ A /\ E)
	 * = (B \/ (C /\ D) \/ (C /\ E)) /\ A
	 * = (B \/ (C /\ (D \/ E))) /\ A
	 * 
	 * @see ompca.condition.Proposition#andByReduce(ompca.condition.Proposition)
	 */
	protected Proposition andByReduce(Proposition p2) {
		assert p2 != null;
		Proposition result = null;
		if (p2.getOp() == Operator.Imply) result = andByReduce((Imply) p2);
		if (result != null) return result;

		/*
		 * (Fx(A -> C) || B) && A
		 * = (Fx(~A || C) || B) && Ex(A)	...given A depends on ONLY x as Fx
		 * = (((~A1 || C1) && (~A2 || C2) &&...&& (~An || Cn)) || B) && (A1 || A2 ||...|| An)
		 * = (~A1 || C1 || B) && (~A2 || C2 || B) &&...&& (~An || Cn || B) && (A1 || A2 ||...|| An)
		 * = (~A1 || C1 || B) && (~A2 || C2 || B) &&...&& (~An || Cn || B) && (A1 || A2 ||...|| An)	
		 * 	...(~X || Y) && (X || Z) = (~X || Y) && (X || Z) = (~X && (X || Z)) || (Y && (X || Z)) = ??
		 * = ignoresDependency
		 */
		final List<Forall> fs = new ArrayList<>();
		ReductionOperations ros = new ReductionOperations();
		ros.add(Operator.Or, (this_, b)-> false, null, null);
		ros.add("(Fx(A -> C) || B) && A = ignoresDependency	...given A depends on ONLY x as Fx",
				Predicate.Operator.Forall, (Fx, X)-> !fs.add((Forall) Fx), null, null);
		ros.add(Operator.Imply, 
				(X, XI)-> p2.equals(((Imply) XI).antecedent), null, null, 
				(X, newXI) -> {if (p2.dependsOnTheSame(fs)) ignoreDependency(Operator.And, p2); return null;});
		result = reduceByOperands(ros, false);
		if (result != null) return result;

		List<Proposition> B = new ArrayList<>();
		boolean isReduced = false;
		for (Proposition b : getPropositions()) {
			// (B \/ A) /\ A = A
			if (b.equals(p2)) return p2;
			
			if (!isReduced) {
				// (B \/ ~A) /\ A = B /\ A
				if (b.equals(p2.not())) {isReduced = true; continue;}
				
				if (b.getOp().equals(Operator.And)) {
					List<Proposition> C = new ArrayList<>();
					C: for (Proposition c : b.getPropositions()) {
						if (!isReduced) {
							// (B \/ (C /\ A)) /\ A = (B \/ C) /\ A
							if (c.equals(p2)) {isReduced = true; continue;}
							
							else if (c.getOp() == Operator.Or) {
								List<Proposition> D = new ArrayList<>();
								for (Proposition d : c.getPropositions()) {
									// (B \/ (C /\ (D \/ A))) /\ A = (B \/ C) /\ A
									if (d.equals(p2)) {isReduced = true; continue C;}
									
									// (B \/ (C /\ (D \/ (E /\ A)))) /\ A = (B \/ (C /\ (D \/ E))) /\ A
									if (d.getOp() == Operator.And) {
										List<Proposition> E = new ArrayList<>();
										for (Proposition e : d.getPropositions()) {
											if (e.equals(p2)) isReduced = true;
											else E.add(e);
										}
										if (isReduced) d = And.from(E);
									}
									D.add(d);
								}
								if (isReduced) c = from(D);
							}
						}
						C.add(c);
					}
					if (isReduced) b = And.from(C);
				}
			}
			B.add(b);
		}
		assert !B.isEmpty();
		return isReduced ? from(B).and(()-> p2) : super.andByReduce(p2);
	}

	private Proposition andByReduce(Imply p2) {
		Proposition p2c = p2.consequent;
		if (p2c.getOp() == Operator.And) {
			boolean isReduced = false; 
			Proposition A = null, B = p2.antecedent, E = null;
			List<Proposition> C = new ArrayList<>(), D = new ArrayList<>();
			// (A \/ D)	/\ (B -> (C /\ (A -> E))) 
			//	= ((~A /\ D) \/ (A /\ (B -> E))) /\ (B -> C)
			for (Proposition d : getPropositions()) {
				if (!isReduced) {
					for (Proposition c : ((And) p2c).getPropositions()) {
						if (c.getOp() == Operator.Imply) {
							Imply ci = (Imply) c;
							E = ci.consequent;
							if (ci.antecedent.equals(d)) {A = d; isReduced = true; continue;} 
						}
						C.add(c);
					}
				}
				D.add(d);
			} 
			if (isReduced) {
				D.remove(A);
				final Proposition A_ = A, E_ = E;
				return A.not().and(D).or(()-> A_.and(()-> B.imply(()-> E_))).and(
						()-> B.imply(()-> And.from(C)));
			}
		}
		return null;
	}
	

	
//	public Proposition or(Predicate pred) {return or(pred);}

	/**
	 * (A \/ B) \/ A
	 * = A \/ B
	 * 
	 * ((A /\ C) \/ B) \/ A
	 * = (A /\ C) \/ B \/ A	...	A C | formula
	 * = B \/ A					0 0 |	0
	 * 							0 1 |	0
	 * 							1 0 |	1
	 * 							1 1 |	1
	 * 
	 * (B \/ (C /\ (D \/ A))) \/ A
	 * = (B \/ A \/ C) /\ (B \/ A \/ D \/ A)
	 * = (B \/ A \/ C) /\ (B \/ A \/ D)
	 * = (B \/ (C /\ D)) \/ A
	 * 
	 * (B \/ (C /\ (D \/ (E /\ A)))) \/ A
	 * = (C /\ (D \/ (E /\ A))) \/ B \/ A
	 * = (C /\ (D \/ E) /\ (D \/ A)) \/ B \/ A
	 * = (C \/ B \/ A) /\ (D \/ E \/ B \/ A) /\ (D \/ A \/ B \/ A)
	 * = (C \/ B \/ A) /\ (D \/ E \/ B \/ A) /\ (D \/ B \/ A)
	 * = (C /\ (D \/ E) /\ D) \/ B \/ A
	 * = (C /\ D) \/ B \/ A
	 * = (B \/ (C /\ D)) \/ A
	 * 
	 * (B \/ (C /\ (D \/ (E /\ (F \/ A))))) \/ A
	 * = (B \/ A \/ C) /\ (B \/ A \/ D \/ (E /\ (F \/ A)))
	 * = (B \/ A \/ C) /\ (B \/ A \/ D \/ E) /\ (B \/ A \/ D \/ F \/ A)
	 * = (B \/ A \/ C) /\ (B \/ A \/ D \/ E) /\ (B \/ A \/ D \/ F)
	 * = B \/ A \/ (C /\ (D \/ E) /\ (D \/ F))
	 * = (B \/ (C /\ (D \/ (E /\ F)))) \/ A
	 * 
	 * ((C -> A) \/ B) \/ A
	 * = ~C \/ A \/ B \/ A
	 * = ~C \/ B \/ A
	 * = (C -> B) \/ A
	 * 
	 * (((A \/ D) -> C) \/ B) \/ A
	 * = ~(A \/ D) \/ C \/ B \/ A
	 * = (~A /\ ~D) \/ C \/ B \/ A
	 * = ((~A \/ A) /\ (~D \/ A)) \/ C \/ B
	 * = ~D \/ A \/ C \/ B
	 * = (D -> C) \/ B \/ A
	 * 
	 * @see ompca.condition.Proposition#orByReduce(ompca.condition.Proposition)
	 * @see ompca.condition.And#andByReduce(ompca.condition.Proposition)
	 */
	protected Proposition orByReduce(Proposition p2) {
		if (p2 == null) throwNullArgumentException("p2");

		final Supplier<Proposition> p2sp = ()-> p2;
		boolean isReduced = false, isReduced2 = false;
		List<Proposition> B = new ArrayList<>();
		Proposition newC = null;
		B: for (Proposition b : getPropositions()) {
			// (F \/ B) \/ A = B \/ A
			if (b.isFalse()) continue;
			
			// (A \/ B) \/ A = A \/ B
			if (b.equals(p2)) return this;
			
			// (A \/ B) \/ ~A = T
			if (!p2.enters()) if (b.equals(p2.not()) || b.isTrue()) 
				return True.from("(A || B) || ~A = T", Operator.Or, this, p2);
			
			if (!isReduced) {
				if (p2.getOp().equals(Operator.And)) {
					Proposition result = orByReduce((And) p2, b);
					if (result != null) return result;
				}
				
				Relation.Operator bOp = b.getOp();
				/*
				 * (B || Fx(A)) || A
				 * = B || Fx(A) || Ex(A)	...given A depends on ONLY x as Fx
				 * = B || A
				 */
				if (bOp.equals(Predicate.Operator.Forall) && p2.dependsOnTheSame((Forall) b)) {
					isReduced = true; continue B;
					
				} else if (bOp instanceof Operator) {
					List<Proposition> C = new ArrayList<>();
					switch ((Operator) bOp) {
					case And:
						for (Proposition c : b.getPropositions()) {
							/*
							 * ((A /\ C) \/ B) \/ A = B \/ A
							 * 
							 * ((C && Fx(A)) || B) || A
							 * = ((C && Fx(A)) || B) || Ex(A)	...given A depends on ONLY x as Fx
							 * = (C && A1 && A2 &&...&& An) || B || A1 || A2 ||...|| An
							 * = (C || B || A1 || A2 ||...|| An) && (A1 || B || A1 || A2 ||...|| An) 
							 * 		&& (A2 || B || A1 || A2 ||...|| An) &&...&& (An || B || A1 || A2 ||...|| An)
							 * = (C || B || A1 || A2 ||...|| An) && (B || A1 || A2 ||...|| An) 
							 * = B || A1 || A2 ||...|| An		...(X || Y) && X = X
							 * = B || A 
							 */
							final Relation.Operator cOp = c.getOp();
							if (c.equals(p2) || 
									(cOp.equals(Predicate.Operator.Forall) && p2.dependsOnTheSame((Forall) c))) {
								isReduced = true; continue B;}
							
							if (cOp.equals(Operator.Or)) {
								List<Proposition> D = new ArrayList<>();
								D: for (Proposition d : c.getPropositions()) {
									if (!isReduced) {
										// (B \/ (C /\ (D \/ A))) \/ A = (B \/ (C /\ D)) \/ A
										if (d.equals(p2)) {isReduced = true; continue;}
										
										if (d.getOp() == Operator.And) {
											List<Proposition> E = new ArrayList<>();
											for (Proposition e : d.getPropositions()) {
												// (B \/ (C /\ (D \/ (E /\ A)))) \/ A 
												//	= (B \/ (C /\ D)) \/ A
												if (e.equals(p2)) {isReduced = true; continue D;}
												
												// (B \/ (C /\ (D \/ (E /\ (F \/ A))))) \/ A 
												//	= (B \/ (C /\ (D \/ (E /\ F)))) \/ A
												if (e.getOp() == Operator.Or) {
													List<Proposition> F = new ArrayList<>();
													for (Proposition f : e.getPropositions()) {
														if (f.equals(p2)) isReduced = true;
														else F.add(f);
													}
													if (isReduced) e = from(F);
												}
												E.add(e);
											}
											if (isReduced) d = And.from(E);
										}
									}
									D.add(d);
								}
								if (isReduced) c = from(D);
							}
							C.add(c);
						}
						if (isReduced) b = And.from(C);
						break;
						
					case Imply:
						Imply bi = (Imply) b;
						final Proposition bia = bi.antecedent, bic = bi.consequent;
						
						// ((C -> A) \/ B) \/ A = (C -> B) \/ A
						if (bic.equals(p2)) {
							newC = bia; isReduced2 = isReduced = true; continue B;}
						
						// (((A \/ C) -> D) \/ B) \/ A = (C -> D) \/ B \/ A
						if (bia.getOp() == Operator.Or) {
							for (Proposition c : bia.getPropositions()) {
								if (c.equals(p2)) isReduced = true;
								else C.add(c);
							}
							if (isReduced) b = from(C).imply(()-> bic);
						}
						break;
						
					// ~A \/ B = A -> B
					case Not: return b.not().imply(p2sp);
					default:
					}
				}
			}
			B.add(b);
		}

		if (isReduced) {
			Supplier<Proposition> newB = ()-> from(B);
			if (isReduced2) return newC.imply(newB).or(p2sp);
			// ((A /\ C) \/ B) \/ A = B \/ A
			return newB.get().or(p2sp);
		}
		return super.orByReduce(p2);
	}
	
//protected Proposition orByReduce(And newProp) {
//for (Proposition p : newProp.getPropositions()) props.add(p.not());
//not();
//}
	
//	protected Proposition orByReduce(Or newProp) {
//		Proposition newPropOrP = new Or(newProp).or(p);
//		if (!(p.equals(newPropOrP))) {
//			propToRemove = p;	// flattening the hierarchical Or result
//			propToAdd = newPropOrP;
//			npIsOr = newPropOrP.getOp() == Operator.Or;
//			traversedProps.add(newPropOrP);
//			break traverseProps;
//		} else return this;	// p == p \/ newProp ==> newProp == FALSE or p
//	}
	
// TODO: optimization by merging same order relations and variable ranges 
//protected Proposition orByReduce(OrderRelation newProp) {
//}

	/**
	 * (A \/ B) \/ (A /\ C)
	 * = A \/ B \/ (A /\ C)
	 * = (A \/ B \/ A) /\ (A \/ B \/ C)
	 * = (A \/ B \/ F) /\ (A \/ B \/ C)
	 * = A \/ B \/ (F /\ C)
	 * = A \/ B
	 * 
	 * (A \/ B) \/ (C /\ (A -> D))
	 * = A \/ B \/ (~A /\ C) \/ (C /\ D)
	 * = B \/ ((A \/ ~A) /\ (A \/ C)) \/ (C /\ D)
	 * = B \/ A \/ C \/ (C /\ D)
	 * = (B \/ A) \/ C
	 * 
	 * (A \/ B) \/ (C /\ Fx(D -> A))
	 * = A \/ (~A /\ ~Fx(A) /\ (B \/ (C /\ Fx(~D))))
	 * 		...when the goal is to make A/Fx(D->A) a singleton			
	 * 			A Fx(D->A)	| Ex(D/\~A)	formula	| Fx(A) | Ex(~A) Fx(D->A) formula
	 * 			0 0			|	1		B		|	0	|	1	 Fx(~D)		B\/(C/\Fx(~D))
	 * 			0 1			|	0		B\/C	|	1	|	0	 -			-
	 * 			1 0			|	1		1		|	0	|	1	 Fx(~D)		1
	 * 			1 1			|	0		1		|	1	|	0	 1			1
	 * = (A \/ ~Fx(A)) /\ (A \/ B \/ (C /\ Fx(~D))))
	 * = ((A \/ ~Fx(A)) /\ A) \/ ((A \/ ~Fx(A)) /\ B) \/ ((A \/ ~Fx(A)) /\ C /\ Fx(~D))
	 * = A \/ (~Fx(A) /\ A) \/ (A /\ B) \/ (~Fx(A) /\ B) \/ ((A \/ ~Fx(A)) /\ C /\ Fx(~D))
	 * = A \/ (~Fx(A) /\ B) \/ ((A \/ ~Fx(A)) /\ C /\ Fx(~D))
	 * = A \/ (~Fx(A) /\ B) \/ (A /\ C /\ Fx(~D)) \/ (~Fx(A) /\ C /\ Fx(~D))
	 * = A \/ (~Fx(A) /\ B) \/ (~Fx(A) /\ C /\ Fx(~D))
	 * = A \/ (~Fx(A) /\ (B \/ (C /\ Fx(~D))))
	 * 
	 * @param newProp
	 * @param b
	 * @return
	 */
	private Proposition orByReduce(And newProp, Proposition b) {
		Proposition A = null;
		Imply ci = null; 
		List<Proposition> B = new ArrayList<>(), Cs = new ArrayList<>();
		Set<VariablePlaceholder<?>> cfqs = null;
		boolean isReduced = false;
		
		for (Proposition c : ((And) newProp).getPropositions()) {
			if (cfqs == null) {
				Relation.Operator cOp = c.getOp();
				
				// (A \/ B) \/ (A /\ C) = A \/ B
				if (c.equals(b)) return this;
				
				// (A \/ B) \/ (C /\ (A -> D)) = (B \/ A) \/ C
				else if (cOp == Operator.Imply 
						&& ((Imply) c).antecedent.equals(b)) {
					isReduced = true; continue;
				}
				// (A \/ B) \/ (C /\ Fx(D -> A)) = A \/ (~Fx(A) /\ (B \/ (C /\ Fx(~D))))
				else if (cOp == Predicate.Operator.Forall) {
					Forall cf = (Forall) c;
					Expression cfp = cf.getFirstOperand();
					if (cfp instanceof Imply) {
						ci = (Imply) cfp;
						A = ci.consequent;
						if (A.equals(b)) {
							cfqs = (Set<VariablePlaceholder<?>>) cf.getQuantifiers();
							isReduced = true; continue;
						}
					}
				}
			}
			Cs.add(c);
		}
		
		// (A \/ B) \/ (C /\ Fx(D -> A)) = A \/ (~Fx(A) /\ (B \/ (C /\ Fx(~D))))
		final Supplier<Proposition> C = ()-> And.from(Cs);
		if (cfqs != null) {
			final Imply ci_ = ci;
			final Proposition A_ = A;
			final Set<VariablePlaceholder<?>> cfqs_ = cfqs;
			return A.or(()-> Forall.from(cfqs_, A_).not().and(()-> 
			Or.from(B).or(()-> C.get().and(()-> Forall.from(cfqs_, ci_.antecedent.not())))));
		}
		
		return isReduced ? or(C) : null;
	}
	
	
	
	/**
	 * TODO: moving the following reduction to {@link Proposition#imply(Proposition)}
	 * 
	 * Flattening hierarchy:
	 * 
	 * (A \/ B) -> B
	 * = ~(A \/ B) \/ B
	 * = (~A /\ ~B) \/ B
	 * = (~A \/ B) /\ (~B \/ B)
	 * = ~A \/ B
	 * = A -> B
	 * 
	 * <br>
	 * <p> TODO: This is an IMMUTABLE operation. 
	 * (Mutable ones are limited to Not.not(), And.and(...), Or.or(...), Imply.imply(...) and 
	 * Iff.iff(...) ONLY)
	 * 
	 * @see ompca.condition.Proposition#implyByReduce(ompca.condition.Proposition)
	 */
	protected Proposition implyByReduce(Proposition consq) {
		if (consq == null) throwNullArgumentException("consq");
		
		Proposition result = null;
		if (consq.getOp() == Operator.Or) result = implyByReduce((Or) consq);
		if (result != null) return result;
		
		boolean isReduced = false;
		List<Proposition> Bs = new ArrayList<>();
		for (Proposition a : getPropositions()) {
			// (A \/ B) -> B = A -> B
			if (!isReduced && a.equals(consq)) isReduced = true;
			else Bs.add(a);
		}
		final Supplier<Proposition> consqSp = ()-> consq;
		if (isReduced) return from(Bs).imply(consqSp);

		// doing the rest optimization if not isReduced
		@SuppressWarnings("unchecked")
		List<Proposition> subA = (List<Proposition>) toList();

		if (dependsOn(consq, null) != null) {
			subA.remove(consq);
			return from(subA).imply(consqSp);
		}
		return super.implyByReduce(consq);
	}
	
	/**
	 * (A \/ B) -> (A \/ C)
	 * = ~(A \/ B) \/ A \/ C
	 * = (~A /\ ~B) \/ A \/ C
	 * = (~A \/ A \/ C) /\ (~B \/ A \/ C)
	 * = ~B \/ A \/ C
	 * = B -> (A \/ C)
	 * 
	 * @param p2
	 * @return
	 */
	private Proposition implyByReduce(Or p2) {
		assert p2 != null;
		
		@SuppressWarnings("unchecked")
		List<Proposition> B = (List<Proposition>) toList();
		boolean isReduced = false;
		for (Proposition c : p2.getPropositions()) 
			if (B.contains(c)) {
				B.remove(c);
				isReduced = true;
			} 
		return isReduced ? from(B).imply(()-> p2) : null;
	}
	

	
	/**
	 * @see ompca.condition.Proposition#notByReduce()
	 */
	protected Proposition notByReduce() {
		final List<Proposition> notProps = reduceByDeMorgan();
		return notProps.isEmpty()
				? null
				: And.from(notProps);
	}

	
	
	public Expression reduceOnce() {
		if (hasOnlyOperand()) return getFirstOperand();
		super.reduceOnce();
		return this;
	}
	
	
	
//	@Override
//	public String toZ3SmtString(boolean printsVariableDeclaration, boolean printsFunctionDefinition) {
//		Iterable<Proposition> props = getPropositions();
//		if (props == null) return null;
//
//		String cond = "";
//		for (Proposition prop : props) cond += (prop.toZ3SmtString(false, false) + " "); 
//		return "(or " + cond + ")";
//	}

}
