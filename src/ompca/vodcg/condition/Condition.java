/**
 * 
 */
package ompca.vodcg.condition;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;

import ompca.Elemental;
import ompca.vodcg.ASTAddressable;
import ompca.vodcg.SystemElement;
import ompca.vodcg.UncertainException;
import ompca.vodcg.UncertainPlaceholderException;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.Relation.Operator;
import ompca.vodcg.condition.data.ArithmeticGuard;
import ompca.vodcg.condition.data.Pointer;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public abstract class Condition 
extends ConditionElement implements SideEffectElement {

//	private static final Map<And, Condition> CONDITIONS = new HashMap<>();
	
	private static final Method METHOD_REDUCE_ONCE = 
			Elemental.getMethod(Condition.class, "reduceOnce");

	private Supplier<Proposition> assertion = null;

	/**
	 * @param scopeManager
	 */
	protected Condition(final ASTAddressable dynaAddr, VODCondGen scopeManager) {
		super(dynaAddr, scopeManager);
		setGlobal();
	}

	// TODO: performance bottleneck!
//	protected static Condition get(And assertions) {
//		if (assertions == null) return null;
//		return CONDITIONS.get(assertions);
//	}
//	
//	protected static void set(Condition cond) {
//		if (cond == null) return;
//		
//		And assr = cond.assertions;
//		if (assr == null) CONDITIONS.values().remove(cond);
//		else CONDITIONS.put(assr, cond);
//	}
	
	@Override
	protected Object cloneNonConstant() {
		Condition clone = (Condition) super.cloneNonConstant();
		clone.assertion = assertion;
		return clone;
	}
	
	
	
	public Supplier<Proposition> getAssertion() {
		return assertion;
	}
	
	public void setAssertion(Supplier<Proposition> newAssert) {
		if (assertion == newAssert || 
				(assertion != null && assertion.equals(newAssert))) return;
		
//		final String pre = isEmpty() ? "" : toString(), 
//				post = newAsserts == null ? "" : newAsserts.toString();
//		if (pre.length() > post.length() && tests(isConstant())) Debug.throwReductionException();
		assertion = newAssert;
//		addGuards(newAsserts.get().getArithmeticGuards());
		setDirty();
	}
	

	
	public void add(final Condition cond2) {
		if (cond2 == null) throwNullArgumentException("condition");
		
		final Supplier<Proposition> ass2 = cond2.getAssertion();
		if (assertion == null) assertion = ass2;
		else if (ass2 != null) {
			final Proposition asst = assertion.get(), asst2 = ass2.get();
			if (asst.equals(asst2)) return;
			final Operator op = asst.getOp();
			boolean addsAll = false;
			if (op.equals(asst2.getOp())) {
				if (op instanceof Proposition.Operator) switch ((Proposition.Operator) op) {
				case And:
				case Or:			addsAll = true; break;
				case False:
				case True:			return;
				case FunctionCall:
				case Iff:
				case Imply:
				case Not:
				case Xor:
				default:			break;
				} 
//				else if (op instanceof OrderRelation.Operator) addsAll = true;
//				else throwTodoException("unsupported merging");
			}
			
			if (addsAll) assertion.get().addAll(asst2.getOperands());
			else assertion = ()-> And.from(asst, ass2);
		}
		
		add(cond2.getArithmeticGuards());
	}

	public void add(final ArithmeticGuard guard) {
		addGuard(guard);
	}
	
	private void add(Set<ArithmeticGuard> gs) {
		assert gs != null;
		for (ArithmeticGuard g : gs) add(g);
	}
	
	
	
//	@Override
//	public void addGuard(ArithmeticGuard guard) {
//		if (assertion == null) throwTodoException("empty assertion needs no guards");
//		super.addGuard(guard);
//	}

	@Override
	protected Set<ArithmeticGuard> cacheArithmeticGuards() {
		// updating guards on demand
		return assertion == null
				? Collections.emptySet()
				: assertion.get().getArithmeticGuards();
	}
	
	@Override
	protected Boolean cacheConstant() {
		try {
			return testsSkipNull(()-> 
			assertion.get().isConstant());
			
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	
//	/**
//	 * @return all indirect side-effects.
//	 * @see ompca.condition.ConditionElement#cacheDirectSideEffect()
//	 */
//	@Override
//	protected VOPConditions cacheDirectSideEffect() {
//		return Elemental.getSkipNull(()-> assertion.getSideEffect());
//	}
	
	@Override
	protected Set<Function> cacheDirectFunctionReferences() {
		return assertion == null
				? Collections.emptySet()
				: assertion.get().getDirectFunctionReferences();
	}
	
	/**
	 * @return a non-null set
	 */
	@Override
	protected <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType) {
		final Set<T> dvrs = new HashSet<>();
		if (assertion != null) 
			dvrs.addAll(assertion.get().cacheDirectVariableReferences(refType));
		for (ArithmeticGuard g : getArithmeticGuards()) 
			dvrs.addAll(g.cacheDirectVariableReferences(refType));
		return dvrs;
	}
	
	@Override
	protected Function cacheFunctionScope() {
		return null;
	}

	@Override
	protected ConditionElement cacheScope() {
		ConditionElement scope = null;
		if (assertion != null) scope = assertion.get().getScope();
		for (ArithmeticGuard g : getArithmeticGuards()) 
			scope = getCommonScope(scope, g.getScope());
		return scope;
	}


	
	/**
	 * @return non-null
	 */
	@Override
	public Set<Pointer> getPointers() {
		return assertion == null
				? Collections.emptySet()
				: assertion.get().getPointers();
	}

	
	
//	protected void setDirty() {
//		if (assertion == null) super.setDirty(); // else assertion.reset();
//	}
	
	
	
	public void and(Condition cond2) {
		if (cond2 == null) throwNullArgumentException("condition");
		if (cond2 == this) return;
		
		and(cond2.getAssertion());
//		andGuards(cond2.getArithmeticGuards());
	}

	public void and(Supplier<Proposition> prop) {
		if (prop == null) throwNullArgumentException("proposition");
		try {
			if (assertion == null) setAssertion(prop);
			else {
				// resolving old assertion before updating to a new one
				final Proposition old = assertion.get();
				setAssertion(()-> old.and(prop));
			}
//			setAssertion(assertion == null 
//					? prop 
//					: ()-> assertion.get().and(prop));
//					: debugCallDepth(null, ()-> ()-> assertion.get().and(prop)));
		} catch (Exception e) {
			throwUnhandledException(e);
		}
	}
	
	public void andSkipNull(Supplier<Proposition> prop) {
		if (prop == null) return;
		and(prop);
	}
	
	protected void andGuards(Set<ArithmeticGuard> gs) {
		add(gs);	// TODO: and(gs)
	}

	
	
	public void or(Condition cond2) {
		if (cond2 == null) throwNullArgumentException("condition");
		if (cond2 == this) return;
		
		or(cond2.getAssertion());
		orGuards(cond2.getArithmeticGuards());
	}
	
	public void or(Supplier<Proposition> prop) {
		if (prop == null) throwNullArgumentException("proposition");
		
		if (assertion == null) setAssertion(prop);
		else {
			// resolving old assertion before updating to a new one
			final Proposition old = assertion.get();
			setAssertion(()-> old.or(prop));
		}
//		setAssertion(assertion == null 
//				? prop
//				: ()-> assertion.get().or(prop));
	}
	
	protected void orGuards(Set<ArithmeticGuard> gs) {
		add(gs);	// TODO: or(gs)
	}
	

	
	public void imply(Condition consq) {
		if (consq == null) throwNullArgumentException("consequent");
		if (consq == this) throwTodoException("tautology condition");
		
		imply(consq.getAssertion()); 
		implyGuards(consq.getArithmeticGuards());
	}
	
	public void imply(Supplier<Proposition> consq) {
		if (assertion == null) throwNullArgumentException("assertion");
		if (consq == null) throwNullArgumentException("consequent");
		
		/* Assertion is don't care => assertion may be either T or F:
		 * T -> F = F and F -> F = T causes contradiction
		 * while T -> T = T and F -> T = T doesn't
		 */
		if (assertion == null) {
			final Proposition cq = consq.get();
			if (cq.isFalse()) throwInvalidityException("contradictive antecedent");
			else setAssertion(()-> cq);
		} else {
			// resolving old assertion before updating to a new one
			final Proposition old = assertion.get();
			setAssertion(()-> old.imply(consq));
		}
//		setAssertion(()-> assertion.get().imply(consq));
	}
	
	protected void implyGuards(Set<ArithmeticGuard> gs) {
		add(gs);	// TODO: imply(gs)
	}

	public void not() {
		if (assertion == null) throwNullArgumentException("assertion");

		// resolving old assertion before updating to a new one
		final Proposition old = assertion.get();
		setAssertion(()-> old.not());
	}

	
	
	/* (non-Javadoc)
	 * @see ompca.condition.ConditionElement#isEmpty()
	 */
	@Override
	public boolean isEmpty() {
		final boolean isE = assertion == null || assertion.get().isSemanticallyEmpty();
//		if (isE && !getArithmeticGuards().isEmpty()) throwTodoException("empty assertion with non-empty guards");
		return isE;
	}
	
	public boolean containsEmpty() {
		return isEmpty() || assertion.get().containsEmpty();
	}
	
	
	
	@Override
	public boolean equalsGlobal() {
//		return true;
		return !testsNot(()-> 
		getScope().equalsGlobal());	// null or globalScope <=> isGlobal
	}
	
	@Override
	protected boolean equalsToCache(SystemElement e2) {
		final Condition cond2 			 = (Condition) e2;
		final Supplier<Proposition> ass2 = cond2.assertion;
		return super.equalsToCache(cond2) 
				&& (assertion == null ? ass2 == null : assertion.get().equals(ass2.get()));
	}
	
	/**
	 * Only depending on the hash codes of assertion.
	 */
	@Override
	protected List<Integer> hashCodeVars() {
		List<Integer> vars = new ArrayList<>();
		vars.add(assertion != null ? assertion.hashCode() : 0);
		return vars;
	}
	
	@Override
	public boolean suitsSideEffect() {
		return assertion != null && assertion.get().suitsSideEffect();
	}

	
	
	/**
	 * Mutable reduction.
	 * 
	 * @see ompca.vodcg.SystemElement#reduceOnce()
	 */
	@SuppressWarnings("unchecked")
	protected Condition reduceOnce() {
		if (assertion != null) assertion = ()-> assertion.get().reduce(METHOD_REDUCE_ONCE);
		super.reduceOnce();
		return this;
	}


	
	/**
	 * @return a separated (excluding this condition) VOP condition-set of side-effect.
	 * @throws UncertainException
	 * @throws UncertainPlaceholderException
	 */
	final public VODConditions collectSideEffect() 
			throws UncertainException, UncertainPlaceholderException {
		final VODConditions se = new VODConditions(null, getCondGen());
		
		if (assertion != null) {
			final Proposition asst = assertion.get();
			se.addFrom(()-> asst.getSideEffect(), asst);
		}
		
		for (ArithmeticGuard g : getArithmeticGuards()) {
			if (g == null) throwNullArgumentException("guard");
			se.addFrom(()-> g.getSideEffect(), g);
		}
		return se;
	}
	
	protected <T extends SideEffectElement> boolean suitsSideEffect(T newSe) {
		final boolean ss = super.suitsSideEffect(newSe);
		if (!(newSe instanceof Condition)) return ss;
		
		return ss && suitsSideEffect(((Condition) newSe).getAssertion().get());
	}

	
	
	@Override
	@SuppressWarnings("unchecked")
	public <T extends ConditionElement> T substitute(Reference<?> ref1, Reference<?> ref2) {
		if (assertion != null) 
			assertion.get().substitute(ref1, ref2);
		for (ArithmeticGuard g : getArithmeticGuards()) 
			g.substitute(ref1, ref2);
		return (T) this;
	}
	

	
	@SuppressWarnings("unchecked")
	protected Condition toConstantIf() {
		return assertion != null && assertion.get().isConstant() ? this : null;
	}

	
	
	private String toZ3SmtAssertion(final TrySupplier<String, ? extends Exception> assSup) {
		assert assSup != null;
		try {
			final String ass = assSup.get();
			return ass == null || ass.isBlank()
					? throwTodoException("empty assertion")
					: "(assert " + ass + ")";
					
		} catch (Exception e) {
			return throwTodoException(e);
		}
	}
	
	private String toZ3SmtAssertion(final Proposition asrt) {
		assert asrt != null;
		try {
//			final IASTStatement pb = asrt.getPrivatizingBlock();
//			if (pb == null) 
				return toZ3SmtAssertion(()-> asrt.toZ3SmtString(false, false, false));
			
//			final ConditionElement asrt1 = asrt.cloneReversion(pb, ThreadRole.THREAD1, null),
//					asrt2 = asrt.cloneReversion(pb, ThreadRole.THREAD2, null);
//			return 
//					asrt1.toZ3SmtVariableDeclaration() + "\n" + 
//					toZ3SmtAssertion(()-> asrt1.toZ3SmtString(false, false)) + "\n" +
//					asrt2.toZ3SmtVariableDeclaration() + "\n" + 
//					toZ3SmtAssertion(()-> asrt2.toZ3SmtString(false, false));
			
		} catch (Exception e) {
			return throwTodoException(e);
		}
	}
	
	public String toZ3SmtAssertions() {
		if (assertion == null) return null;
		
		String cond = "";
		final Proposition asst = assertion.get();
		// for the well-formed assertion format.
		if (asst instanceof And)
			for (Proposition asrt : asst.getPropositions()) {
				if (asrt.isSemanticallyEmpty()) continue;
				cond += ("\n" + toZ3SmtAssertion(asrt));
			}
		else cond = toZ3SmtAssertion(asst);
		return cond;
	}
	
	@Override
	public String toZ3SmtString(boolean printsVariableDeclaration, 
			boolean printsFunctionDefinition, boolean isLhs) {
		// for variable and function declarations/definitions
		String cond = printsVariableDeclaration || printsFunctionDefinition
						? toZ3SmtAssertions() : assertion.get().toZ3SmtString(false, false, isLhs);
		for (ArithmeticGuard g : getArithmeticGuards()) 
			cond += ("\n" + g.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition, isLhs));
		return super.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition, isLhs) 
				+ "\n" 
				+ cond;
	}

}