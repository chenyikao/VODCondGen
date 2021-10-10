/**
 * 
 */
package ompca.vodcg;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IFunction;

import ompca.Elemental;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.FunctionCall;
import ompca.vodcg.condition.FunctionalPathVariable;
import ompca.vodcg.condition.PathVariable;
import ompca.vodcg.condition.version.FunctionalVersion;
import ompca.vodcg.condition.version.NoSuchVersionException;
import ompca.vodcg.condition.version.ThreadRole;
import ompca.vodcg.condition.version.Version;
import ompca.vodcg.parallel.OmpDirective;

/**
 * Assignable is given a type argument to distinguish Assignable<PathVariable> and Assignable<FunctionalPathVariable>
 * since it can't implement both VersionEnumerable<PathVariable> and VersionEnumerable<FunctionalPathVariable>.
 *  
 * @author Kao, Chen-yi
 *
 */
public class FunctionalAssignable extends FunctionAssignable {

	private static final Method METHOD_GET_DEPENDENT_LOOPS = 
			Elemental.getMethod(FunctionalAssignable.class, "getDependentLoops");
//	private static final Method METHOD_TESTS_UBIQUITY = 
//			Elemental.getMethod(FunctionalAssignable.class, "testsUbiquity", Function.class, Boolean.class);

	
	
	private FunctionalVersion fv = null;
	
	/**
	 * Constructor for the assignable with a virtual function call
	 * @param asnPv
	 */
	protected FunctionalAssignable(Assignable<PathVariable> asnPv) {
		super(getNonNull(()-> asnPv.getASTName()), 
				null, 
				asnPv.getNameOwner(), 
				null, 
				asnPv.getCondGen());
		
		if (asnPv.getBinding() instanceof IFunction) throwTodoException("non-virtual functional assignable");
	}
	
//	protected FunctionalAssignable(
//			IASTName name, IFunction bind, IASTNameOwner owner, Supplier<VODCondGen> condGen) 
//					throws ASTException {
//		super(name, bind, owner, condGen);
//	}


	
	@Override
	public ThreadRole initRole() {
		return ThreadRole.FUNCTION;
	}

	@Override
	protected Boolean cacheConstant() {
		return false;
//		return getVersion().isConstant();
	}

	@Override
	public FunctionCall<?> getCallView() {
		return getVersion().getFuncCallView();
	}

	/**
	 * @return @NotNull
	 */
	@Override
	public List<IASTStatement> getDependentLoops() {
//		if (enters(METHOD_GET_DEPENDENT_LOOPS)) return Collections.emptyList();
		
//		enter(METHOD_GET_DEPENDENT_LOOPS);
		final List<IASTStatement> sls = super.getDependentLoops();
		if (isLoopIterator()) return sls;
		
		final List<IASTStatement> loops = new ArrayList<>(sls);
		
		// re-entered by getVersion() -> FunctionalVersion.from(...)
		guard(()-> loops.addAll(getVersion().getLoops()));
		// for (possibly non-array) ubiquitous function which depends on loops elsewhere
		testsUbiquity(asn-> loops.addAll(asn.getDependentLoops()), false);
//		leave(METHOD_GET_DEPENDENT_LOOPS);
		
		return !loops.isEmpty() || enters(METHOD_GET_DEPENDENT_LOOPS)
				? loops 
				: throwTodoException("functional assignable without loops");
	}

	@Override
	public Set<Assignable<?>> getDirectAssigners() {
		return getNonASTFunctionDirectAssigners();
//		final Set<Assignable<?>> asgrs = new HashSet<>();
//		for (Version<?> v : 
//			getVersion().getAssigner().getDirectVariableReferences())
//			asgrs.add(v.getAssignable());
//		return asgrs;
	}

	@Override
	public FunctionCall<?> getEnclosingCall() throws ASTException {
		return getVersion().getFuncCallView();
	}

	@Override
	public IASTStatement getPrivatizingBlock() {
		final VODCondGen cg = getCondGen();
		for (IASTStatement loop : ASTLoopUtil.toNavigableSet(
				getVersion().getLoops(), cg).descendingSet()) 
			if (testsNot(()-> OmpDirective.from(loop, cg).isEmpty())) return loop;
		return null;
	}

	/**
	 * @return @NotNull
	 */
	@Override
	public FunctionalVersion getVersion() {
		if (fv != null) return fv;
		
		try {
			return fv = (FunctionalVersion) FunctionalVersion.from(this);
		} catch (NoSuchVersionException e) {
			return throwTodoException(e);
		}
	}
	
	/**
	 * @return @NotNull
	 */
	@Override
	public Set<Assignable<?>> getArguments() {
		final Set<Assignable<?>> args = new HashSet<>();
		for (ArithmeticExpression arg : debugGet(()-> getVersion().getArguments())) 
			for (Version<?> argv : arg.getDirectVariableReferences()) try {
				addSkipNull(args, ()-> argv.getAssignable());
			} catch (Exception e) {
				throwTodoException(e);
			}
		return args; 
	}

	/**
	 * @return true always for its meaning
	 */
	@Override
	public boolean hasArguments() {
		return true;
	}

//	@Override
//	public boolean isConditionalTo(IASTStatement branch) {
//		return guard(
//				()-> getVersion().getLoops().contains(branch),
//				()-> super.isConditionalTo(branch));
//	}

	@Override
	public boolean isASTFunction() {
		return false;
	}

	@Override
	public boolean isConditionalTo(IASTForStatement branch) {
		return super.isConditionalTo(branch)
				|| testsUbiquity(asn-> asn.isConditionalTo(branch), true);
	}
	
//	@Override
//	public boolean isThreadPrivate() {
//		return true;
//	}
	
	@Override
	public Boolean isFunctional() {
		return true;
	}
	
	public void setFunctionalVersion(FunctionalVersion fv) {
		this.fv = fv;
	}

//	@SuppressWarnings("unchecked")
//	@Override
//	public Assignable<FunctionalPathVariable> previous() throws IncomparableException {
//		final Assignable<FunctionalPathVariable> p = super.previous().toFunctional();
//		setPrevious(p);
//		return p;
//	}
	
	@Override
	protected void setPrevious(Assignable<FunctionalPathVariable> pasn) {
		super.setPrevious(pasn);
	}

	@Override
	protected Assignable<FunctionalPathVariable> previousOrNext(
			IASTNode root, final Boolean findsNext, Boolean findsLocally) throws IncomparableException {
		final Assignable<FunctionalPathVariable> spon = super.previousOrNext(root, findsNext, findsLocally);
		return spon == null
				? null
				: debugGetNonNull(()-> spon.toFunctionalIf());
	}
	
	
	
	/**
	 * @param func
	 * @param interrupts
	 * @return
	 */
	private boolean testsUbiquity(Predicate<Assignable<?>> func, boolean interrupts) {
		assert func != null;
		if (!isArray()) for (Assignable<?> asd : getAssigneds()) {
			if (asd == this || asd.enters(METHOD_GET_DEPENDENT_LOOPS)) continue;
			asd.enter(METHOD_GET_DEPENDENT_LOOPS);
			if (func.test(asd) && interrupts) return true;
			asd.leave(METHOD_GET_DEPENDENT_LOOPS);
		}
		
//		if (loops.isEmpty()) for (Assignable<?> asn :getOnesEqualsVariable()) {
//		for (Assignable<?> asn : getOthersEqualsVariable()) {
		for (Assignable<?> asn : getOtherAssignedsEqualsVariable()) {
			if (asn == this || asn.enters(METHOD_GET_DEPENDENT_LOOPS)) continue;
			asn.enter(METHOD_GET_DEPENDENT_LOOPS);
			if (func.test(asn) && interrupts) return true;
			asn.leave(METHOD_GET_DEPENDENT_LOOPS);
		}
		return false;
		
//		if (!enters(METHOD_TESTS_UBIQUITY)) {
//			enter(METHOD_TESTS_UBIQUITY);
//			leave(METHOD_TESTS_UBIQUITY);
//		}
	}
	
	
	
	@Override
	protected FunctionalAssignable toFunctionalIf() {
		return this;
	}
	
}