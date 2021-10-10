/**
 * 
 */
package ompca.vodcg.condition;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTForStatement;

import ompca.vodcg.ASTAddressable;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.ReductionOperations.ReductionOctet;

/**
 * Quantification	::= 'forall' (Variable ',')+
 * 
 * @author Kao, Chen-yi
 *
 */
public class Forall extends Predicate {

	private Forall(Set<VariablePlaceholder<?>> quantifiers, Proposition prop) {
		super(Operator.Forall, quantifiers, prop);	// prop.checkDependency(this);
		setFinal();
	}
	
//	public static Forall from(Variable quantifier, Collection<Proposition> conjProp) {
//	super(quantifier, conjProp, quantifier.scope);
//}

	/**
	 * Convenient construction method for AST for-loop.
	 * 
	 * @param stat
	 * @return
	 */
	public static Proposition from(IASTForStatement stat, final ASTAddressable rtAddr, VODCondGen condGen) {
		if (stat == null) throwNullArgumentException("for-loop");
		
		final Proposition pre = Proposition.fromRecursively(stat.getInitializerStatement(), rtAddr, condGen),
				itRange = ExpressionRange.fromIteratorOf(stat, rtAddr, condGen),
				body = Proposition.fromRecursively(stat.getBody(), rtAddr, condGen);
		return itRange instanceof ExpressionRange
				? pre.and(()-> from(Arrays.asList((ExpressionRange<?>) itRange), body))
				: pre.and(itRange).and(body);
	}
	
	/**
	 * Factory method to avoid a self-recurring {@link Forall}.
	 * 
	 * @param quantifiers
	 * @param prop
	 * @return
	 */
	public static Proposition from(Set<VariablePlaceholder<?>> quantifiers, Proposition prop) {
		return from(Operator.Forall, quantifiers, prop, ()-> new Forall(quantifiers, prop));	// prop.checkDependency(fa);
	}

	/**
	 * Factory method to avoid a self-recurring {@link Forall}.
	 * 
	 * @param expRanges
	 * @param prop
	 * @return
	 */
	public static Proposition from(
			List<ExpressionRange<? extends Expression>> expRanges, 
			Proposition prop) {
		return from(Operator.Forall, expRanges, prop, qs-> new Forall(qs, prop));	// prop.checkDependency(fa);
	}



	protected Proposition andByReduce(Proposition p2) {
		if (p2 == null) throwNullArgumentException("p2");
		
		final Proposition prop = getProposition();
		/*
		 * Fx(A) && A
		 * = Fx(A) && Ex(A)	...given A depends on ONLY x as Fx(A)
		 * = Fx(A)
		 */
		if (prop.equals(p2) && p2.dependsOnTheSame(this)) return this;
		
		final List<Forall> fs = new ArrayList<>(Arrays.asList(this));
		final ReductionOperations ros = new ReductionOperations();
		/*
		 * Fx(B && A) && A
		 * = Fx(B) && A && A	...given A in-depends on x
		 * = Fx(B) && A
		 */
		final ReductionOctet faAnd = new ReductionOctet(
				"Fx(B && A) && A = Fx(B) && A	...given A in-depends on x",
				Proposition.Operator.And, (B, b)-> b.equals(p2), null, null, (B, newB)-> And.from(newB)),
		/*
		 * Fx(B && (C -> A)) && A
		 * = Fx(B && (~C || A)) && Ex(A)	...given A depends on ONLY x as Fx
		 * = B1 && (~C1 || A1) && B2 && (~C2 || A2) &&...&& Bn && (~Cn || An) && (A1 || A2 ||...|| An)
		 * = (B1 && (~C1 || A1) && B2 && (~C2 || A2) &&...&& Bn && (~Cn || An) && A1) || 
		 * 		(B1 && (~C1 || A1) && B2 && (~C2 || A2) &&...&& Bn && (~Cn || An) && A2) ||...|| 
		 * 		(B1 && (~C1 || A1) && B2 && (~C2 || A2) &&...&& Bn && (~Cn || An) && An)
		 * = (B1 && A1 && B2 && (~C2 || A2) &&...&& Bn && (~Cn || An)) || 
		 * 		(B1 && (~C1 || A1) && B2 && A2 &&...&& Bn && (~Cn || An)) ||...|| 
		 * 		(B1 && (~C1 || A1) && B2 && (~C2 || A2) &&...&& Bn && An)	...(X || Y) && Y = Y
		 * = (B1 && (~T || A1) && B2 && (~C2 || A2) &&...&& Bn && (~Cn || An)) || 
		 * 		(B1 && (~C1 || A1) && B2 && (~T || A2) &&...&& Bn && (~Cn || An)) ||...|| 
		 * 		(B1 && (~C1 || A1) && B2 && (~C2 || A2) &&...&& Bn && (~T || An))
		 * = (Fx(B && (C -> A)) && C1=T) || (Fx(B && (C -> A)) && C2=T) ||...|| (Fx(B && (C -> A)) && Cn=T)
		 * = Fx(B && (C -> A)) && (C1=T || C2=T ||...|| Cn=T)
		 * = Fx(B && (C -> A)) && C
		 * = ignoresDependency
		 * 
		 * Fx(B -> A) && A
		 * = Fx(~B || A) && Ex(A)	...given A depends on ONLY x as Fx
		 * = (~B1 || A1) && (~B2 || A2) &&...&& (~Bn || An) && (A1 || A2 ||...|| An)
		 * = ((~B1 || A1) && (~B2 || A2) &&...&& (~Bn || An) && A1) || 
		 * 		((~B1 || A1) && (~B2 || A2) &&...&& (~Bn || An) && A2) ||...|| 
		 * 		((~B1 || A1) && (~B2 || A2) &&...&& (~Bn || An) && An)
		 * = (A1 && (~B2 || A2) &&...&& (~Bn || An)) || 
		 * 		((~B1 || A1) && A2 &&...&& (~Bn || An)) ||...|| 
		 * 		((~B1 || A1) && (~B2 || A2) &&...&& An)		...(X || Y) && Y = Y
		 * = ((~T || A1) && (~B2 || A2) &&...&& (~Bn || An)) || 
		 * 		((~B1 || A1) && (~T || A2) &&...&& (~Bn || An)) ||...|| 
		 * 		((~B1 || A1) && (~B2 || A2) &&...&& (~T || An))
		 * = (Fx(B -> A) && B1=T) || (Fx(B -> A) && B2=T) ||...|| ((Fx(B -> A) && Bn=T)
		 * = Fx(B -> A) && (B1=T || B2=T ||...|| Bn=T)
		 * = Fx(B -> A) && B
		 * = ignoresDependency
		 * 
		 * Fx(B -> Fy(A -> C)) && A
		 * = Fx(~B || Fy(~A || C)) && A
		 * = Fx(~B || Fy(~A || C)) && Exy(A)	...given A depends on ONLY x and y as Fxy
		 * = Fx(~B || ((~Ay1 || Cy1) && (~Ay2 || Cy2) &&...&& (~Ayn || Cyn))) && Exy(A)
		 * = ignoresDependency
		 */
		faImply = new ReductionOctet(
				"Fx(B && (C -> A)) && A 			 = ignoresDependency	...given A depends on ONLY x as Fx\n"
				+ "Fx(B -> A) && A = A && Fx(B -> A) = ignoresDependency\n"
				+ "Fx(A -> B) && A = A && Fx(A -> B) = ignoresDependency	...given A depends on ONLY x as Fx",
				Proposition.Operator.Imply, (X, xi)-> p2.equals(xi), null, (X, xi)-> ((Imply) X).consequent, 
				(X, XI) -> p2.dependsOnTheSame(fs) ? 
						ignoreDependency(Proposition.Operator.And, p2) : returnIndependencyException());
		ros.addPrimDisj(faAnd, faImply);
		ros.addPrimDisj(new ReductionOctet(
				"Fx(B -> Fy(A -> C)) && A = ignoresDependency	...given A depends on ONLY x and y as Fxy",
				Operator.Forall, (Bconsq, Y)-> !fs.add((Forall) Bconsq), null, null, null),
		/*
		 * Fx(B -> (C && A)) && A
		 * = Fx(~B || (C && A)) && Ex(A)	...given A depends on ONLY x as Fx
		 * = (~B1 || (C1 && A1)) && (~B2 || (C2 && A2)) &&...&& (~Bn || (Cn && An)) && (A1 || A2 ||...|| An)
		 * = (~B1 || (C1 && A1)) && (~B2 || (C2 && A2)) &&...&& (~Bn || (Cn && An)) && (A1 || A2 ||...|| An)
		 * = ignoresDependency
		 * 
		 * Fx(B -> (C && Fy(D -> A))) && A
		 * = Fx(~B || (C && Fy(~D || A))) && Exy(A)	...given A depends on ONLY x and y as Fxy
		 * = Fx(~B || (C && (~Dy1 || Ay1) && (~Dy2 || Ay2) &&...&& (~Dym || Aym))) && Exy(A)
		 * = ignoresDependency
		 * 
		 * Fx(B -> Fy(C -> (A && D))) && A
		 * = Fx(~B || Fy(~C || (A && D))) && Exy(A)	...given A depends on ONLY x and y as Fxy
		 * = Fx(~B || ((~Cy1 || (Ay1 && Dy1)) && (~Cy2 || (Ay2 && Dy2)) &&...&& (~Cyn || (Ayn && Dyn)))) && Exy(A)
		 * = ignoresDependency
		 */
		new ReductionOctet("Fx(B -> (C && A)) && A = ignoresDependency	...given A depends on ONLY x as Fx\n" + 
				"Fx(B -> Fy(C -> (A && D))) && A = ignoresDependency	...given A depends on ONLY x and y as Fxy\n" +
				"Fx(B -> (C && Fy(D -> A))) && A = ignoresDependency	...given A depends on ONLY x and y as Fxy",
				Proposition.Operator.And, (bic, ca)-> p2.equals(ca), null, 
				(bic, ca)-> ca.getOp().equals(Operator.Forall) ? ((Forall) ca).getProposition() : null, 
				(bic, newCA) -> p2.dependsOnTheSame(fs) ? 
						ignoreDependency(Proposition.Operator.And, p2) : returnIndependencyException()));
		Proposition result = prop.reduceByOperands(ros, true);
		if (result != null) return from(quantifiers, result).and(()-> p2);

//		ros.clear();
//		ros.add(roAnd);
//		ros.add(roImply);
//		result = prop.reduceByOperands(ros, false);
//		if (result != null) return result;

		if (p2.getOp() == getOp()) {
			Forall fa2 = (Forall) p2;
			if (quantifiers.equals(fa2.getQuantifiers())) {
				result = andByReduceQuantifiers(fa2);
				if (result != null) return result;

				result = fa2.andByReduceQuantifiers(this);
				if (result != null) return result;
			}

			/*
			 * Fx(A) /\ Fy(Fx(A) /\ B) = p2 => Fy(Fx(A) /\ B) /\ Fx(A) = this
			 *
			 * Fx(A) /\ Fy(Fz(Fx(A))) = p2 	=> Fy(Fz(Fx(A))) /\ Fx(A) = this
			 * 
			 * Fx(A) /\ Fy(Fz(Fw(Fv(Fu(Fx(A)) /\ C)) /\ B)) = p2 
			 * => Fy(Fz(Fw(Fv(Fu(Fx(A)) /\ C)) /\ B)) /\ Fx(A) = this
			 *
			 * Fx(A) /\ Fy(B /\ Fz(Fw(Fv(Fu(C /\ Ft(D /\ Fx(A))))))) = ??
			 * 
			 * Fx(A) /\ Fy(Fz(Fw(Fv(Fu(Ft(Fx(A)) /\ B))))) = p2
			 * => Fy(Fz(Fw(Fv(Fu(Ft(Fx(A)) /\ B))))) /\ Fx(A) = this
			 */
			result = fa2.andByReduceForall(this);
			if (result != null) return result;
		} 
		
		result = andByReduceForall(p2);
		return result == null ? super.andByReduce(p2) : result;
	}
	
	protected Proposition andByReduceForall(Proposition p2) {
		return andByReduceForall(p2, this);
	}
	
	/**
	 * @param p2
	 * @param forall - the beginning for matching Forall
	 * @return this if matched p2; null if not
	 */
	protected Proposition andByReduceForall(Proposition p2, Proposition forall) {
//		if (forall != this) return super.andByReduceForall(p2, forall);
		
		/*
		 * Fy(Fx(A) /\ B) /\ Fx(A)
		 * = Fyx(A) /\ Fy(B) /\ Fx(A)
		 * = Fyx(A) /\ Fy(B) /\ EyFx(A)
		 * = Fyx(A) /\ Fy(B)	...Ex(A) /\ Fx(A) = Fx(A)
		 * = this
		 * 
		 * Fy(B /\ Fz(Fx(A) /\ C)) /\ Fx(A)
		 * = Fy(B /\ Fzx(A) /\ Fz(C)) /\ Fx(A)
		 * = Fy(B) /\ Fyzx(A) /\ Fyz(C) /\ Fx(A)
		 * = Fy(B) /\ Fyzx(A) /\ Fyz(C) /\ EyzFx(A)
		 * = Fy(B) /\ Fyzx(A) /\ Fyz(C) 	...Fx(A) /\ Ex(A) 
		 * 									= (A1/\A2/\.../\An) /\ (A1\/A2\/...\/An)
		 * 									= (A1/\A2/\.../\An/\A1) \/ (A1/\A2/\.../\An/\A2) \/...\/ (A1/\A2/\.../\An/\An)
		 * 									= (A1/\A2/\.../\An) \/ (A1/\A2/\.../\An) \/...\/ (A1/\A2/\.../\An)
		 * 									= (A1/\A2/\.../\An) = Fx(A)
		 * = this
		 * 
		 * Fx(B && Fy(A && C)) && A
		 * = Fx(B && Fy(A && C)) && Exy(A)	...given A depends on ONLY x and y
		 * = Fx(B && (Ay1 && Cy1) && (Ay1 && Cy1) &&...&& (Aym && Cym)) && (Ax1y1 || Ax1y2 ||...|| Axnym)
		 * = ignoresDependency
		 * 
		 * Fx(B && Fy(A && C)) && A
		 * = Fx(B && A && Fy(C)) && Ex(A)	...given A depends on ONLY x
		 * = B1 && A1 && Fy(C1) && B2 && A2 && Fy(C2) &&...&& Bn && An && Fy(Cn) && (A1 || A2 ||...|| An)
		 * = this
		 * 
		 * Fx(B && Fy(A && C)) && A
		 * = A && Fx(B && Fy(C)) && A	...given A independs on both x and y
		 * = Fx(B && Fy(C)) && A
		 * 
		 * Fx(B /\ Fy(Fz(A /\ D) /\ C)) /\ A
		 * = Fx(B /\ Fy(Fz(A) /\ Fz(D) /\ C)) /\ A
		 * = Fx(B /\ Fyz(A) /\ Fyz(D) /\ Fy(C)) /\ A
		 * = Fx(B) /\ Fxyz(A) /\ Fxyz(D) /\ Fxy(C) /\ A
		 * = Fx(B) /\ Fxyz(A) /\ Fxyz(D) /\ Fxy(C) /\ Exyz(A)
		 * = Fx(B) /\ Fxyz(A) /\ Fxyz(D) /\ Fxy(C) 	...Fx(A) /\ Ex(A) = Fx(A)
		 * = this
		 * 
		 * Fx(Fy(C /\ Fz(Fw(E /\ A) /\ D)) /\ B) /\ A
		 * = this
		 */
		final List<Forall> fs = new ArrayList<>(Arrays.asList(this));
		final ReductionOperations ros = new ReductionOperations();
		final ReductionOctet 
		roAnd1 = new ReductionOctet("Fx(B && Fy(A && C)) && A = this				...given A depends on ONLY x",
				Proposition.Operator.And, (Y, c)-> c.equals(p2), null, null, 
				(Y, newC)-> p2.dependsOnTheSame(this) ? ros.setReduced(0, 0, this) : null),
		roAnd2 = new ReductionOctet("Fx(B && Fy(A && C)) && A = Fx(B && Fy(C)) && A	...given A independs on both x and y",
				Proposition.Operator.And, (Y, c)-> c.equals(p2), null, null, 
				(Y, newC)-> p2.independsOn(fs) ? ros.setReduced(0, 1, And.from(newC)) : null),
		roAnd3 = new ReductionOctet("Fx(B && Fy(A && C)) && A = ignoresDependency	...given A depends on ONLY x and y",
				Proposition.Operator.And, (Y, c)-> c.equals(p2), null, null, 
				(Y, newC)-> p2.dependsOnTheSame(fs) ? ignoreDependency(Proposition.Operator.And, p2) : null),
		roForall = new ReductionOctet(Operator.Forall, (b, Y)-> !fs.add((Forall) b), null, null, 
				(b, newY)-> roAnd1.isReduced() ? this 
						: (roAnd2.isReduced() ? Forall.from(((Forall) b).quantifiers, newY.get(0)) : null));
		ros.addPrimDisj(roAnd1, roAnd2, roAnd3);
		ros.addPrim(roForall);
		Proposition result = andByReduceRecursively(p2, ros);
		if (result != null) return result;
		
		fs.clear(); fs.add(this);
		ros.clear();
		/*
		 * Fx(Fy(B -> A)) && A
		 * = Fx(Fy(~B || A)) && Exy(A)	...given A depends on ONLY x and y as Fxy
		 * = Fx((~By1 || Ay1) && (~By2 || Ay2) &&...&& (~Bym || Aym)) && Exy(A)
		 * = ignoresDependency
		 */
		ros.add("Fx(Fy(B -> A)) && A = ignoresDependency	...given A depends on ONLY x and y as Fxy",
				Operator.Forall, (X, Y)-> !fs.add((Forall) Y), null, (X, Y)-> ((Forall) Y).getProposition(), null);
		ros.add(Proposition.Operator.Imply, (Y, YI)-> ((Imply) YI).consequent.equals(p2), null, 
				(Y, newYI)-> p2.dependsOnTheSame(fs) ? ignoreDependency(Proposition.Operator.And, p2) : null);
		result = getProposition().reduceByOperands(ros, false);
		if (result != null) return result;

		ros.clear();
		/*
		 * Fy(Fz(Fx(A))) /\ Fx(A)
		 * = Fyzx(A) /\ Fx(A)
		 * = Fyzx(A) /\ EyzFx(A)
		 * = Fyzx(A) 	...Fyz(Fx(A)) /\ Eyz(Fx(A)) = Fyz(Fx(A)) 
		 * = this
		 */
		final ReductionOctet
		roForall2 = new ReductionOctet("Fy(Fx(A)) && Fx(A) = this",
				Operator.Forall, (Fy, Y)-> Y.equals(p2), null, null, (Fy, Y)-> this);
		ros.addPrimDisj(roAnd1, roForall2);
//		/*
//		 * Fy(Fz(Fw(Fv(Fu(Fx(A)) /\ C)) /\ B)) /\ Fx(A) 
//		 * = Fy(Fz(Fw(Fv(Fux(A) /\ C)) /\ B)) /\ Fx(A)
//		 * = Fy(Fz(Fw(Fvux(A) /\ Fv(C)) /\ B)) /\ Fx(A)
//		 * = Fy(Fz(Fwvux(A) /\ Fwv(C) /\ B)) /\ Fx(A)
//		 * = Fy(Fzwvux(A) /\ Fzwv(C) /\ Fz(B)) /\ Fx(A)
//		 * = Fyzwvux(A) /\ Fyzwv(C) /\ Fyz(B) /\ Fx(A)
//		 * = Fyzwvux(A) /\ Fyzwv(C) /\ Fyz(B) /\ EyzwvuFx(A)
//		 * = Fyzwvux(A) /\ Fyzwv(C) /\ Fyz(B)	...Ex(A) /\ Fx(A) = Fx(A)
//		 * = this
//		 */
//		ros = new ReduceOperations();
//		ros.addPrim(forallRq);		// Fz
//		ros.addPrim(andRq);			// B
//		ros.addPrim(forallRq);		// Fw
//		ros.addPrim(forallRq);		// Fv
//		ros.addPrim(andRq);			// C
//		ros.addPrim(forallP2Rq);	// Fu
//		result = andByReduceRecursively(p2, ros);
//		if (result != null) return result;
//
//		/*
//		 * Fy(B /\ Fz(Fw(Fv(Fu(C /\ Ft(D /\ Fx(A))))))) /\ Fx(A)
//		 * = ??Fy(B /\ Fz(Fw(Fv(Fu(C /\ Ft(D /\ Fx(A))))))) /\ Fx(A)
//		 * 
//		 * Fy(Fz(Fw(Fv(Fu(Ft(Fx(A)) /\ B))))) /\ Fx(A)
//		 * = Fy(Fz(Fw(Fv(Fu(Ftx(A) /\ B))))) /\ Fx(A)
//		 * = Fy(Fz(Fw(Fv(Futx(A) /\ Fu(B))))) /\ Fx(A)
//		 * = Fy(Fz(Fw(Fvutx(A) /\ Fvu(B)))) /\ Fx(A)
//		 * = Fy(Fz(Fwvutx(A) /\ Fwvu(B))) /\ Fx(A)
//		 * = Fy(Fzwvutx(A) /\ Fzwvu(B)) /\ Fx(A)
//		 * = Fyzwvutx(A) /\ Fyzwvu(B) /\ Fx(A)
//		 * = Fyzwvutx(A) /\ Fyzwvu(B) /\ EyzwvutFx(A)
//		 * = Fyzwvutx(A) /\ Fyzwvu(B) 	...Fyzwvut(Fx(A)) /\ Eyzwvut(Fx(A)) = Fyzwvut(Fx(A))
//		 * = this 
//		 */
//		ros = new ReduceOperations();
//		ros.addPrim(forallRq);		// Fz
//		ros.addPrim(forallRq);		// Fw
//		ros.addPrim(forallRq);		// Fv
//		ros.addPrim(forallRq);		// Fu
//		ros.addPrim(andRq);			// B
//		ros.addPrim(forallP2Rq);	// Ft
		result = andByReduceRecursively(p2, ros);
		if (result != null) returnTodoException("given A depends on ONLY x and y");
		return result;
	}

	@SuppressWarnings("unlikely-arg-type")
	private Proposition andByReduceQuantifiers(Forall fa2) {
		assert fa2 != null;
		assert quantifiers.equals(fa2.getQuantifiers());
		
		/*
		 * Fx(Fx(A)) /\ Fx(A) = Fx(A) /\ Fx(Fx(A)) 
		 * = Fx(A) /\ Fxx(A) = Fx(A)
		 * 
		 * Fx(Fx(A) /\ B) /\ Fx(A) = Fx(A) /\ Fx(Fx(A) /\ B)
		 * = Fx((A1/\A2/\.../\An) /\ B) /\ Fx(A)			...literal substitution
		 * = (A1/\A2/\.../\An) /\ Fx(B) /\ Fx(A)			...literal out
		 * = Fx(A) /\ Fx(B) /\ Fx(A)
		 * = Fx(A) /\ Fx(B)
		 * = Fx(A /\ B)
		 * 
		 * Fx(B /\ Fy(C /\ Fx(A))) /\ Fx(A)
		 * = Fx(B /\ Fy(C) /\ Fyx(A)) /\ Fx(A)
		 * = Fx(B) /\ Fxy(C) /\ Fyx(A) /\ Fx(A)
		 * = Fx(B) /\ Fxy(C) /\ Fx(A)			...if x.contains(y)
		 * = Fx(B /\ Fy(C)) /\ Fx(A)
		 * 
		 * Fx(A) /\ Fx(B /\ Fy(C /\ Fx(A)))
		 * = Fx(A) /\ Fx(B /\ Fy(C) /\ Fyx(A))
		 * = Fx(A) /\ Fx(B) /\ Fxy(C) /\ Fyx(A)
		 * = Fx(A) /\ Fx(B) /\ Fxy(C) 			...if x.contains(y)
		 * = Fx(A) /\ Fx(B /\ Fy(C))
		 */
		ReductionOperations ros = new ReductionOperations();
		ros.add("Fx(Fx(A) && B) 			&& Fx(A) 	= Fx(A && B)\n" + 
				"oprd = Fx(A) && B, 		oprd2 = A, 	result = B\n" +
				"Fx(B && Fy(C && Fx(A))) 	&& Fx(A) 	= Fx(B && Fy(C)) && Fx(A)\n" + 
				"oprd = B && Fy(C && Fx(A)),oprd2 = A,	result = B && Fy(C)",
				Proposition.Operator.And, 
				(Fx, b)-> b.equals(fa2), null, null, (Fx, newB)-> And.from(newB));
		// Fy, for non-recurrent prop 
		ros.add(Operator.Forall, null, null, (Fy, newC)-> quantifiers.contains(((Forall) Fy).quantifiers) ? 
				returnTodoException("!x.contains(y)") : Forall.from(quantifiers, newC.get(0)));
//		ros.add(Proposition.Operator.And, new ReduceQuartet(false, true, 
//				prop -> prop.equals(fa2), (parent, props) -> And.get(props)));
		Proposition result = andByReduceRecursively(fa2, ros);
		if (ros.isReduced(0)) 
			return Forall.from(quantifiers, ((Proposition) fa2.getFirstOperand()).and(()-> result)); 
//		if (ros.isReduced(2)) {
//			setOnlyOperand(result);
//			return and(fa2);
//		}
		return null;
		
		/*
		 * Fx(A) /\ Fx(B /\ Fy(C /\ Fz(D /\ Fx(A)))) 
		 * = Fx(A) /\ Fx(B /\ Fy(C /\ Fz(D) /\ Fzx(A))) 
		 * = Fx(A) /\ Fx(B /\ Fy(C) /\ Fyz(D) /\ Fyzx(A)) 
		 * = Fx(A) /\ Fx(B) /\ Fxy(C) /\ Fxyz(D) /\ Fyzx(A) 
		 * = Fx(A) /\ Fx(B) /\ Fxy(C) /\ Fxyz(D) 	...if x.contains(y) /\ x.contains(z)
		 * = Fx(A) /\ Fx(B /\ Fy(C) /\ Fyz(D))
		 * = Fx(A) /\ Fx(B /\ Fy(C /\ Fz(D)))
		 * 
		 * ros[0]: Fx(A) /\ Fx(Fx(A)) 				= Fx(A)
		 * 	oprd = A, oprd2 = Fx(A),				result = null
		 * ros[1]: Fx(A) /\ Fx(Fx(A) /\ B) 			= Fx(A /\ B)
		 * 	oprd = A, oprd2 = Fx(A) /\ B,			result = B
		 * ros[3]: Fx(A) /\ Fx(B /\ Fy(C /\ Fx(A))) = Fx(A) /\ Fx(B /\ Fy(C))
		 * 	oprd = A, oprd2 = B /\ Fy(C /\ Fx(A)),	result = B /\ Fy(C)
		 * ros[5]: Fx(A) /\ Fx(B /\ Fy(C /\ Fz(D /\ Fx(A)))) = Fx(A) /\ Fx(B /\ Fy(C /\ Fz(D)))
		 * 	oprd = A, oprd2 = B /\ Fy(C /\ Fz(D /\ Fx(A))),	result = B /\ Fy(C /\ Fz(D))
		 */
//		ros = new ReduceOperations();
//		ros.add(Operator.Forall, new ReduceQuartet(false, true, 
//				prop -> prop.equals(this), (parent, props) -> props.get(0)));
//		ros.add(Proposition.Operator.And, new ReduceQuartet(false, true, 
//				prop -> prop.equals(this), (parent, props) -> And.get(props)));
//		ros.add(Operator.Forall, rqFy);
//		ros.add(Proposition.Operator.And, new ReduceQuartet(false, true, 
//				prop -> prop.equals(this), (parent, props) -> And.get(props)));
//		ros.add(Operator.Forall, new ReduceQuartet(false, false, null, 
//				(parent, props) -> {
//					if (quantifiers.contains(((Predicate) parent).quantifiers)) 
//						Debug.throwTodoException("!x.contains(z)");
//					parent.setOnlyOperand(props.get(0)); return parent;}));
//		ros.add(Proposition.Operator.And, new ReduceQuartet(false, true, 
//				prop -> prop.equals(this), (parent, props) -> And.get(props)));
//		result = fa2.reduceByOperands(ros);
//		if (ros.isReduced(0)) return this;	// result == null
//		if (ros.isReduced(1)) {
//			result.checkDependency(op, oprd); 
//			setOnlyOperand(oprd.and(result)); 
//			return this;
//		}
//		if (ros.isReduced(3) || ros.isReduced(5)) {setOnlyOperand(result);}
	}

	/**
	 * @param p2 
	 * @param ros
	 * @return
	 */
	private Proposition andByReduceRecursively(Proposition p2, ReductionOperations ros) {
		Proposition result = null, prop = getProposition();
		while (true) {
			/* oprd' /\ Fx(A) = (oprd /\ Fx(A)) /\ Fx(A) = oprd /\ Fx(A) /\ Fx(A) 
			 * = oprd /\ Fx(A)
			 */
			result = prop.reduceByOperands(ros, true);
			if (result == null) return null;
			if (result != this && result.dependsOn(p2) != null) prop = result;
			else break;
		}
		return result;
	}
	

	
	protected Proposition orByReduce(Proposition p2) {
		if (p2 == null) throwNullArgumentException("p2");
		
		/*
		 * Fx(A) || A
		 * = Fx(A) || Ex(A)	...given A depends on ONLY x as Fx
		 * = (A1 && A2 &&...&& An) || A1 || A2 ||...|| An
		 * = (A1 || A2 ||...|| An || A1) && (A1 || A2 ||...|| An || A2) &&...&& 
		 * 		(A1 || A2 ||...|| An || An)
		 * = (A1 || A2 ||...|| An) && (A1 || A2 ||...|| An) &&...&& 
		 * 		(A1 || A2 ||...|| An)
		 * = A
		 */
		if (p2.dependsOnTheSame(this)) return p2;
		return null;
	}

	
	
	@Override
	public String toNonEmptyString(boolean usesParenthesesAlready) {
		return "Forall" + quantifiers.toString() + 
				"(" + getFirstOperand().toNonEmptyString(true) + ")";
	}



	/**
	 * TODO: reusing {@link Proposition#toZ3SmtString(boolean, boolean, boolean)} to handle locals.
	 * 
	 * @see ompca.condition.ConditionElement#toZ3SmtString()
	 */
	@Override
	public String toZ3SmtString(boolean printsVariableDeclaration, 
			boolean printsFunctionDefinition, boolean isLhs) {
		if (quantifiers == null) return null;
		else {
			String qs = "";
			for (VariablePlaceholder<?> q : quantifiers) qs += q.toZ3SmtString(true, true, isLhs);
			return "(forall (" + qs + ") " 
					+ getFirstOperand().toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition, isLhs) 
					+ ")";
		}
	}

}