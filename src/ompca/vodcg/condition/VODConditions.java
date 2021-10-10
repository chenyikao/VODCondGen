package ompca.vodcg.condition;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;

import ompca.Elemental;
import ompca.condition.SerialFormat;
import ompca.solver.CarryInRangeDegrader;
import ompca.solver.CarryInRangeDegrader.Parameter;
import ompca.vodcg.ASTAddressable;
import ompca.vodcg.SystemElement;
import ompca.vodcg.UncertainException;
import ompca.vodcg.UncertainPlaceholderException;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.data.ArithmeticGuard;
import ompca.vodcg.condition.data.DataType;
import ompca.vodcg.condition.data.FiniteNumberGuard;
import ompca.vodcg.condition.data.Pointer;
import ompca.vodcg.parallel.OmpDirective;

/**
 * A VOP condition set combines both parallel and path condition with 
 * Z3 top-level functions.
 * 
 * VOPConditions ::= ParallelCondition && PathCondition
 * 
 * @author Kao, Chen-yi
 * 
 */
@SuppressWarnings("deprecation")
public class VODConditions 
extends ConditionElement implements SideEffectElement {

	private static final Method METHOD_REDUCE_ONCE = 
			Elemental.getMethod(VODConditions.class, "reduceOnce");

	private ParallelCondition paraCond;
	private PathCondition pathCond;
	private PathCondition raceCond;
	
	

	/**
	 * Specific constructor for VOPConditions itself as the scope.
	 *  
	 * @param rtAddr 
	 * @param scopeManager
	 */
	public VODConditions(final ASTAddressable rtAddr, VODCondGen scopeManager) {
		super(rtAddr, scopeManager);
		
//		isGlobal = true;
		setScope(()-> this);
	}
	
	public VODConditions(Proposition assertion) {
		this(null, PathCondition.from(assertion), assertion.getCondGen());
	}

	public VODConditions(ParallelCondition paraCond, PathCondition pathCond, 
			VODCondGen scopeManager) {
		super(null, scopeManager);
		
		init(paraCond, pathCond);
//		setScope(scope);
	}
	
	private void init(ParallelCondition paraCond, PathCondition pathCond) {
		this.paraCond = paraCond;
		this.pathCond = pathCond;
//		collectSideEffect();
	}
	
	public void clone(final VODConditions conds2) {
		if (conds2 == null) throwNullArgumentException("conditions to clone");
		
		init(conds2.paraCond, conds2.pathCond);
	}
	
	@Override
	protected Object cloneNonConstant() {
		VODConditions clone = (VODConditions) super.cloneNonConstant();
		clone.paraCond = paraCond;
		clone.pathCond = pathCond;
		return clone;
	}
	
	
	
	/**
	 * @return @NotNull 
	 * 	a separated (excluding this condition) VOP condition-set of side-effect.
	 */
	private VODConditions collectSideEffect() {
		final VODConditions se = new VODConditions(null, getCondGen());
		
		// collecting all side-effect parallel conditions
		if (getParallelCondition() != null) {
			ParallelCondition sePara = paraCond.collectSideEffect().paraCond;
			if (paraCond == null) paraCond = sePara;
			else if (sePara != null) paraCond.add(sePara);
		}
		
		// collecting all side-effect before outputting 
		if (getPathCondition() != null) {
			// collecting all side-effect path conditions
			PathCondition sePath = pathCond.collectSideEffect().pathCond;
			if (pathCond == null) pathCond = sePath;
			else if (sePath != null) pathCond.add(sePath);
		}
		
		// collecting all side-effect race conditions
		if (getRaceCondition() != null) {
			PathCondition seRace = raceCond.collectSideEffect().raceCond;
			if (raceCond == null) raceCond = seRace;
			else if (seRace != null) raceCond.add(seRace);
		}
		
		return se;
	}

	

	@Override
	public String getIDSuffix(SerialFormat format) {
		return get(()-> getParallelCondition().getIDSuffix(format),
				()-> throwTodoException("not identifiable"));
	}
	

	
	public ParallelCondition getParallelCondition() {
		return paraCond;
	}

	public PathCondition getPathCondition() {
		if (pathCond == null) pathCond = new PathCondition(null, getScopeManager());
		return pathCond;
	}
	
	public PathCondition getRaceCondition() {
		if (raceCond == null) raceCond = applySkipNull(
				race-> PathCondition.from(race), ()-> generateRaceConditions());
		return raceCond;
	}
	
	/**
	 * @return non-null all side-effect parallel conditions.
	 */
	public Set<ParallelCondition> getAllParallelConditions() 
			throws UncertainException {
		try {
			final Set<ParallelCondition> pcs = new HashSet<>();
			addSkipNull(pcs, ()-> getParallelCondition());
			
			for (PathVariablePlaceholder pvp : getDirectPathVariablePlaceholders())
				for (OmpDirective dir : pvp.getAssignable().getEnclosingDirectives())
					addSkipNull(pcs, ()-> dir.getCondition());

			return pcs;
			
		} catch (UncertainException e) {
			throw e;
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	
	/**
	 * @return direct assertions from both parallel and path conditions.
	 */
	public Supplier<Proposition> getAssertion() {
		Supplier<Proposition> pathAssr = pathCond == null ? null : pathCond.getAssertion();
		if (paraCond == null || paraCond.isEmpty()) return pathAssr;
		
		Supplier<Proposition> paraAssr = paraCond.getAssertion();
		return paraAssr == null ? null : ()-> paraAssr.get().and(pathAssr);
	}
	
	@Override
	protected Set<ArithmeticGuard> cacheArithmeticGuards() {
		Set<ArithmeticGuard> guards = new HashSet<>(); 
		for(ParallelCondition prc : getAllParallelConditions()) 
			guards.addAll(prc.getArithmeticGuards());
		addAllSkipNull(guards, ()-> getPathCondition().getArithmeticGuards());
		addAllSkipNull(guards, ()-> getRaceCondition().getArithmeticGuards());
		return guards;
	}
	
	@Override
	protected ConditionElement cacheScope() {
		ConditionElement scope = null;
		if (paraCond != null) scope = paraCond.getScope();
		if (pathCond != null) scope = getCommonScope(scope, pathCond.getScope());
		if (raceCond != null) scope = getCommonScope(scope, raceCond.getScope());
		return scope;
	}

	
	
	@Override
	protected <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType) {
		final Set<T> vrs = new HashSet<>();
//		for(ParallelCondition prc : getAllParallelConditions()) 
//			vrs.addAll(prc.cacheDirectVariableReferences(refType));
		addAllSkipNull(vrs, ()-> getParallelCondition().cacheDirectVariableReferences(refType));
		addAllSkipNull(vrs, ()-> getPathCondition().cacheDirectVariableReferences(refType));
		addAllSkipNull(vrs, ()-> getRaceCondition().cacheDirectVariableReferences(refType));
		return vrs;
	}
	
	@Override
	protected Set<Function> cacheDirectFunctionReferences() {
		final Set<Function> refs = new HashSet<>();
		addAllSkipNull(refs, ()-> getParallelCondition().getDirectFunctionReferences());
		addAllSkipNull(refs, ()-> getPathCondition().getDirectFunctionReferences());
		addAllSkipNull(refs, ()-> getRaceCondition().getDirectFunctionReferences());
		return refs;
	}
	
	@Override
	public Set<Pointer> getPointers() {
		Set<Pointer> ps = new HashSet<>();
		for(ParallelCondition prc : getAllParallelConditions()) 
			ps.addAll(prc.getPointers());
		addAllSkipNull(ps, ()-> getPathCondition().getPointers());
		addAllSkipNull(ps, ()-> getRaceCondition().getPointers());
		return ps;
	}
	

	
	public void add(VODConditions conds2) {
		if (conds2 == null) throwNullArgumentException("conditions");
		
		final ParallelCondition para2 = conds2.getParallelCondition();
		if (paraCond == null) paraCond = para2;
		else if (para2 != null) paraCond.add(para2);
		
		final PathCondition path2 = conds2.getPathCondition();
		if (pathCond == null) pathCond = path2;
		else if (path2 != null) pathCond.add(path2);
		
		final PathCondition race2 = conds2.getRaceCondition();
		if (raceCond == null) raceCond = race2;
		else if (race2 != null) raceCond.add(race2);
	}
	
	public void add(Function f) {
		if (f == null) throwNullArgumentException("function");
		getPathCondition().add(f);
	}
	
	
	
	public <T extends SideEffectElement> VODConditions and(T newSe) {
		if (newSe instanceof VODConditions) 			return and((VODConditions) newSe);
		else if (newSe instanceof ParallelCondition) 	return and((ParallelCondition) newSe);
		else if (newSe instanceof PathCondition) 		return and((PathCondition) newSe);
		else if (newSe instanceof FiniteNumberGuard) 	return and((FiniteNumberGuard) newSe);
		else if (newSe instanceof Proposition) 			return and(()-> (Proposition) newSe);
		else 
			throwTodoException("unsupported side-effect");
		return null;
	}
	
	public VODConditions and(VODConditions conds) {
		if (conds == null || conds.isEmpty()) throwNullArgumentException("conditions");
		return andSkipNull(conds);
	}
		
	public VODConditions and(ParallelCondition cond) {
		if (paraCond == null) paraCond = cond;
		if (cond != null) paraCond.and(cond);
		return this;
	}
	
	public VODConditions and(PathCondition pathCond2) {
		if (pathCond == null) pathCond = pathCond2;
		if (pathCond2 != null) pathCond.and(pathCond2);
		return this;
	}
	
	/**
	 * Convenient guard-setting method for path condition.
	 * 
	 * @param guard
	 */
	public VODConditions and(FiniteNumberGuard guard) {
		getPathCondition().add(guard);
		return this;
	}
	
	public VODConditions or(Collection<? extends Function> funcs) {
		getPathCondition().and(funcs);
		return this;
	}
	
	public VODConditions and(Supplier<Proposition> prop, BooleanFunction func) {
		getPathCondition().andIn(prop, func);
		return this;
	}
	
	/**
	 * Convenient assertion appending method for path condition.
	 * 
	 * @param prop - the newly appended path assertion.
	 * @return TODO
	 */
	public VODConditions and(Supplier<Proposition> prop) {
		getPathCondition().and(prop);
		return this;
	}
	
//	public void and(Proposition prop) {
//		if (prop == null) throwNullArgumentException("proposition");
//		and(()-> prop);
//	}
	
	/**
	 * @param <T>
	 * @param oriCond - original non-override-able condition
	 * @param seCond - side-effect condition
	 * @return
	 */
	static private <T extends Condition> T and(T oriCond, T seCond) {
		if (oriCond == null) return seCond;
		if (seCond == null) return oriCond;
		
		seCond.and(oriCond);
		return seCond;
	}
	
	/**
	 * 'Add' operation is specific for a condition to expand conjunction of assertions,
	 * while <code>conds1 /\ conds2</code> shrinks <code>conds1</code> potentially.
	 * @param seSup
	 * @param seContainer
	 * 
	 * @return
	 */
	public VODConditions addFrom(Supplier<VODConditions> seSup, SideEffectElement seContainer) 
	throws UncertainException, UncertainPlaceholderException {
		if (seContainer != null && seContainer.suitsSideEffect()) {
			if (seSup == null) throwNullArgumentException("side-effect supplier");
//			final VODConditions se = seSup.get();
			final VODConditions se = debugGet(seSup);
			if (se != null) add(se);
		}
		return this;
	}
	
	private VODConditions andSkipNull(VODConditions conds) {
//		assert conds != null && !conds.isEmpty() &&
//				paraCond2 != null && !paraCond2.isEmpty() &&
//				pathCond2 != null && !pathCond2.isEmpty();
		if (conds == null) return this;
		
		ParallelCondition paraCond2 = conds.getParallelCondition();
		if (paraCond2 != null && !paraCond2.isEmpty()) {
			if (paraCond == null) paraCond = paraCond2; 
			else paraCond.and(paraCond2);
		}
		
		PathCondition pathCond2 = conds.getPathCondition();
		if (pathCond2 != null && !pathCond2.isEmpty()) {
			if (pathCond == null) pathCond = pathCond2; 
			else pathCond.and(pathCond2);
		}

		return this;
	}
	

	
	public <T extends SideEffectElement> void or(T newSe) {
		if (newSe instanceof VODConditions) or((VODConditions) newSe);
		else throwTodoException("unsupported side-effect");
	}
	
	public void or(VODConditions conds) {
		if (conds == null) throwNullArgumentException("conditions");
		orSkipNull(conds);
	}
	
	private void orSkipNull(VODConditions conds) {
		if (conds == null) return;
		
		ParallelCondition paraCond2 = conds.getParallelCondition();
		if (paraCond2 != null) {
			if (paraCond == null) paraCond = paraCond2; 
			else paraCond.or(paraCond2);
		}
		
		PathCondition pathCond2 = conds.getPathCondition();
		if (pathCond2 != null) {
			if (pathCond == null) pathCond = pathCond2; 
			else pathCond.or(pathCond2);
		}
	}
	
	
	
	public VODConditions imply(VODConditions conds) {
		if (conds == null) throwNullArgumentException("consequent condition");
		
		ParallelCondition para2 = conds.getParallelCondition();
		if (paraCond != null && para2 != null) paraCond.imply(para2);
		else if (!(paraCond == null && para2 == null)) throwNullArgumentException("parallel condition");
		
		PathCondition path2 = conds.getPathCondition();
		if (pathCond != null && path2 != null) pathCond.imply(path2);
		else if (!(pathCond == null && path2 == null)) throwNullArgumentException("path condition");
		
		return this;
	}
	

	
	public VODConditions not() {
		try {
			final ParallelCondition para2 = Elemental.getSkipNull(()-> (ParallelCondition) paraCond.clone());
			final PathCondition path2 = Elemental.getSkipNull(()-> (PathCondition) pathCond.clone());
			if (para2 != null) para2.not(); 
			if (path2 != null) path2.not(); 
			return new VODConditions(para2, path2, getScopeManager());
			
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	

	
	/**
	 * @return Disjunction of sub-parallel race conditions.
	 */
	public Proposition generateRaceConditions() {
		Proposition result = null;
		for (ParallelCondition prc : getAllParallelConditions()) {
			final Proposition subResult = prc.generateRaceAssertion();
			result = result == null ? subResult : result.or(()-> subResult);
		}
		
		if (result == null && OmpDirective.hasAny()) 
			log("truly no race?");
//			throwTodoException("truly no race");
		return result;
	}
	
	
	
	@Override
	protected Boolean cacheConstant() {
		try {
			return testsSkipNull(()->
			paraCond != null && paraCond.isConstant()
			&& pathCond != null && pathCond.isConstant());
			
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	
	/* (non-Javadoc)
	 * @see ompca.vodcg.condition.ConditionElement#isEmpty()
	 */
	@Override
	public boolean isEmpty() {
		return (paraCond == null || paraCond.isEmpty())
				&& (pathCond == null || pathCond.isEmpty());
	}
	
	public boolean containsEmpty() {
		return (paraCond != null && paraCond.containsEmpty()) 
				|| (pathCond != null && pathCond.containsEmpty());
	}


	
	protected boolean equalsToCache(SystemElement e2) {
		VODConditions conds2 		= (VODConditions) e2;
		ParallelCondition paraCond2 = conds2.paraCond;
		PathCondition pathCond2 	= conds2.pathCond;
		return super.equalsToCache(conds2) 
				&& (paraCond == null ? paraCond2 == null : paraCond.equals(paraCond2))
				&& (pathCond == null ? pathCond2 == null : pathCond.equals(pathCond2))
				;
	}
	
	/**
	 * Only depending on the hash codes of parallel and path condition.
	 */
	protected List<Integer> hashCodeVars() {
		List<Integer> vars = new ArrayList<>();
		vars.add(paraCond != null ? paraCond.hashCode() : 0);
		vars.add(pathCond != null ? pathCond.hashCode() : 0);
		return vars;
	}

	
	
	/**
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public VODConditions reduceOnce() {
		if (paraCond != null) paraCond.reduce(METHOD_REDUCE_ONCE);
		if (pathCond != null) pathCond.reduce(METHOD_REDUCE_ONCE);
		super.reduceOnce();
		return this;
	}
	
	@Override
	protected <T extends SideEffectElement> boolean suitsSideEffect(T newSe) {
		final boolean ss = super.suitsSideEffect(newSe);
		if (!(newSe instanceof VODConditions)) return ss;
		
		final VODConditions nse = (VODConditions) newSe;
		if (nse.isEmpty()) throwNullArgumentException("parallel or path condition");
		final ParallelCondition nsePara = nse.getParallelCondition();
		final PathCondition nsePath = nse.getPathCondition();
		return ss && ((nsePara != null && suitsSideEffect(nsePara)) 
				|| (nsePath != null && suitsSideEffect(nsePath)));
	}
	
	@SuppressWarnings("unchecked")
	public <T extends ConditionElement> T substitute(Reference<?> ref1, Reference<?> ref2) {
		if (paraCond != null) paraCond.substitute(ref1, ref2);
		if (pathCond != null) pathCond.substitute(ref1, ref2);
		return (T) this;
	}
	

	
	protected String toNonEmptyString(boolean usesParenthesesAlready) {
		String str = "";
		if (paraCond != null) str += paraCond.toString(); 
		if (pathCond != null) str += pathCond.toString();
		return str;
	}

	/* (non-Javadoc)
	 * @see ompca.vodcg.condition.ConditionElement#toZ3SmtString()
	 */
	public String toZ3SmtString(boolean printsVariableDeclaration, 
			boolean printsFunctionDefinition, boolean isLhs) {
		final VODConditions se = collectSideEffect();
		final ParallelCondition sePara = and(paraCond, se.paraCond);
		final PathCondition sePath = and(pathCond, se.pathCond),
				seRace = and(raceCond, se.raceCond);

		// outputting declarations
		final boolean hasSeRace = seRace != null;
		final boolean hasSePara = sePara != null && !sePara.isEmpty();
		String cond = new String(); 
		String param = null;
		if (hasSePara) {
			param =  sePara.getNumThreads().getID(SerialFormat.Z3_SMT); 
			CarryInRangeDegrader.setParam(new Parameter(
					param, DataType.Int, "0", VODCondGen.getPositiveInfinityInt128()));
//				new Parameter(VODCondGen.getSimulatedPositiveInfinityInt(), DataType.Int));
		}
		
		// outputting conditions
		if (hasSePara) {
			cond += "\n\n(define-fun ParallelCondition () Bool (and \n";
			cond += (sePara.toZ3SmtString(false, false, isLhs) + "\n");
			cond += "))\n\n";
			cond += CarryInRangeDegrader.toZ3SmtDeclaration();
		}
		
		if (hasSeRace) {
			cond += "\n\n(define-fun RaceCondition () Bool \n";
			cond += (seRace.toZ3SmtString(false, false, isLhs) + "\n");
			cond += ")\n\n";
		}
		
		if (hasSeRace) cond += "\n\n(assert RaceCondition)";
		if (hasSePara) cond += "\n(assert ParallelCondition)";
		if (sePath != null && !sePath.isEmpty()) {
			String pathAssr = sePath.toZ3SmtAssertions();
			if (pathAssr == null) throwNullArgumentException("path condition");
			cond += ("\n" + pathAssr);
		}
		return super.toZ3SmtString(true, true, isLhs) + cond + "\n\n(check-sat)\n(get-model)\n(exit)";
	}

}