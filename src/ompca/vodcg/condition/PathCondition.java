/**
 * 
 */
package ompca.vodcg.condition;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;

import ompca.Elemental;
import ompca.vodcg.ASTAddressable;
import ompca.vodcg.SystemElement;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.data.Pointer;

/**
 * PathCondition	::= Function* Assertions?
 * Assertions		::= And
 * And				::= Predicate (&& Predicate)*
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class PathCondition extends Condition {

	/**
	 * More like a function cache since every {@link ConditionElement} can get its
	 * {@link Function} references via {@link ConditionElement#getFunctionReferences(Set)}.
	 * 
	 * TODO: merge with cache mechanism of {@link Function} and 
	 * {@link ConditionElement#getFunctionReferences(Set)}.
	 */
	private Set<Function> functions = null;
	
	private Supplier<Proposition> laterConsq = null;
	
	
	
//	TODO: public PathCondition(Set<Proposition> props) {
//		super(\/ props.scope); 
//		if (props != null) assertions = new And(props, scope);
//	}

	private PathCondition(Proposition prop) {
		super(prop.cacheRuntimeAddress(), prop.getScopeManager());

		and(()-> prop);		// constructor needs no delayed computation
	}

	public PathCondition(final ASTAddressable rtAddr, VODCondGen condGen) {
		super(rtAddr, condGen);
	}
	
	public static PathCondition from(Proposition assertions) {
		if (assertions == null) throwNullArgumentException("assertions");
		
//		Condition cond = Condition.get(And.get(assertions));
//		if (cond == null) 
			return new PathCondition(assertions);
//		else if (cond instanceof PathCondition) 
//			return (PathCondition) cond;
//		return null;
	}

	

	/**
	 * @return ONLY explicitly defined non-null functions.
	 */
	public Set<Function> getFunctions() {
		// updating functions first
//		SortedSet<Function> fRefs = getFunctionReferences(null);
//		if (fRefs != null) {
//			if (functions == null) functions = fRefs;
//			else if (functions != fRefs) functions.addAll(fRefs);
//		}
//		
		return functions == null
				? Collections.emptySet()
				: functions;
	}
	
	@Override
	protected <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType) {
		final Set<T> vrs = new HashSet<>(super.cacheDirectVariableReferences(refType));
		
		// TODO: merge three following function caches
		for (Function f : getFunctions()) 
			vrs.addAll(f.cacheDirectVariableReferences(refType));
//		for (Function f : Function.getCOnes()) 
//			vrs.addAll(f.getDirectVariableReferences(refType));
//		for (Function f : BooleanFunction.getAll()) 
//			vrs.addAll(f.getDirectVariableReferences(refType));

		return vrs;
	}
	
	protected Set<Function> cacheDirectFunctionReferences() {
		Set<Function> assFRefs = 
				new HashSet<>(super.cacheDirectFunctionReferences());
		assFRefs.addAll(getFunctions());
		return assFRefs;
	}
	
	@Override
	public Set<Pointer> getPointers() {
		final Set<Pointer> ps = new HashSet<>(super.getPointers());
		try {
			for (Function f : getFunctions()) ps.addAll(f.getPointers());
		} catch (Exception e) {
			throwTodoException(e);
		}
		return ps;
	}
	

	
	/**
	 * 'Add' is better called than 'and' since contradicting functions may co-exist in the same condition.
	 * 
	 * @param func
	 */
	public void add(Function func) {
		if (func == null) throwNullArgumentException("function");
		
		if (functions == null) functions = new HashSet<>();
		functions.add(func);
		setDirty();
	}
	
	public void and(PathCondition cond) {
		if (cond == null || cond.isEmpty()) throwNullArgumentException("condition");
		
		for (Function cf : cond.getFunctions()) add(cf);
		and(cond.getAssertion());
	}
	
	public void and(Collection<? extends Function> funcs) {
		if (funcs == null || funcs.isEmpty()) throwNullArgumentException("functions");
		
		for (Function f : funcs) add(f);
	}
	
	public void andIn(Supplier<Proposition> prop, BooleanFunction func) {
		if (func == null) 
			and(prop);
		else {
			func.and(prop);
			add(func);
		}
	}
	
	public void andImplyIn(
			Supplier<Proposition> antec, Supplier<Proposition> consq, BooleanFunction func) {
		if (antec == null) throwNullArgumentException("antec"); 
		if (consq == null) throwNullArgumentException("consq"); 

		andIn(()-> antec.get().imply(consq), func);
	}
	
	public void andImplyIn(Supplier<Proposition> consq, BooleanFunction func) {
		if (consq == null) throwNullArgumentException("consq"); 

		implyLater(consq);
		Supplier<Proposition> ass = getAssertion();
		andIn(ass == null ? laterConsq : ()-> ass.get().imply(laterConsq), func);
		laterConsq = null;
	}
	
	/**
	 * @param consequent
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public PathCondition imply(PathCondition consequent) {
		try {
			super.imply(consequent);
			Elemental.consumeSkipEmptyCol(
					fs-> and((Collection<? extends Function>) fs), ()-> consequent.getFunctions());
			return this;

		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}

	/**
	 * Updating the assertions with its implication to the given 
	 * proposition {@link #subConsq} and {@link #laterConsq} in the 
	 * given function {@link func}.
	 * 
	 * @param subConsq
	 * @param func
	 */
	public void implyIn(Supplier<Proposition> subConsq, BooleanFunction func) {
		implyLater(subConsq);
		imply(laterConsq);
		laterConsq = null;

		if (func != null) {
			func.and(getAssertion());
			add(func);
		}
	}
	
	public void implyLater(Supplier<Proposition> subConsq) {
		if (subConsq == null) throwNullArgumentException("sub-consq"); 
		
		laterConsq = laterConsq == null 
				? subConsq 
				: ()-> laterConsq.get().and(subConsq);
	}
	
	public void or(PathCondition cond) {
		if (cond == null) throwNullArgumentException("condition"); 
		
		for (Function f : cond.getFunctions()) add(f);
		super.or(cond);
	}
	


	public boolean containsEmpty() {
		for (Function f : getFunctions()) 
			if (f.containsEmpty()) return true;
		return super.containsEmpty(); 
	}
	

	
	protected boolean equalsToCache(SystemElement e2) {
		final PathCondition cond2 	= (PathCondition) e2;
		return super.equalsToCache(cond2) 
				&& getFunctions().equals(cond2.getFunctions());
	}
	
	protected List<Integer> hashCodeVars() {
		List<Integer> vars = new ArrayList<>(super.hashCodeVars());
		vars.add(getFunctions().hashCode());
		return vars;
	}

	
	
	/**
	 * Replacing all assertions by the given function call.
	 * 
	 * @param call
	 */
	public void replaceByCall(FunctionCall<?> call) {
		if (call == null) return;
		
		add(BooleanFunction.from(call.getSubject(), getAssertion().get()));
		setAssertion(()-> call.toProposition());
	}

}