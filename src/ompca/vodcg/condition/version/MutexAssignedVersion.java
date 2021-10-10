/**
 * 
 */
package ompca.vodcg.condition.version;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.NavigableSet;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import ompca.Elemental;
import ompca.vodcg.ASTException;
import ompca.vodcg.Assignable;
import ompca.vodcg.IncomparableException;
import ompca.vodcg.SystemElement;
import ompca.vodcg.UncertainPlaceholderException;
import ompca.vodcg.condition.ConditionElement;
import ompca.vodcg.condition.ConditionalExpression;
import ompca.vodcg.condition.Expression;
import ompca.vodcg.condition.Function;
import ompca.vodcg.condition.PathVariable;
import ompca.vodcg.condition.PathVariablePlaceholder;
import ompca.vodcg.condition.Proposition;
import ompca.vodcg.condition.Variable;
import ompca.vodcg.condition.data.ArithmeticGuard;
import ompca.vodcg.condition.data.Pointer;

/**
 * <pre>
 * Case x ::= (cond ? y : z)		= (cond && x = y) || (!cond && x = z) 
 * Case x ::= (cond ? true : y)		= cond && x = ?						=> uncertain x
 * Case x ::= (cond ? false : y)	= !cond && x = y
 * Case x ::= (cond ? y : true)		= !cond && x = ?					=> uncertain x
 * Case x ::= (cond ? y : false)	= cond && x = y
 * </pre>
 * 
 * <h1>Storing versions for the conditional (non-linear writing) placeholder wh[whi] or constant within branch[whi]</h1>
 * 
 * <pre>
 * Case Independent-branches:
 * ...
 * wh[whi-n] = ...
 * ...
 * branch[whi-2]: {
 * 	...
 * 	wh[whi-2] = ...
 * 	...
 * }
 * ...
 * branch[whi-1]: {
 * 	...
 * 	wh[whi-1] = ...
 * 	...
 * }
 * ...
 * branch[whi]: {
 * 	...
 * 	wh[whi] = ... 
 * 		branch[whi-1].cond 
 * 		? wh[whi-1] 
 * 		: (branch[whi-2].cond 
 * 			? wh[whi-2] : ...) ...
 * 	...
 * }
 * </pre>
 * @author Kao, Chen-yi
 * @see FunctionalVersion FunctionalVersion (for versions under iterations such as for-loops or while-loops)
 *
 */
@SuppressWarnings("deprecation")
public class MutexAssignedVersion extends Version<PathVariable> {

	static private final Set<String> MUTEX_DECLS = new HashSet<>();
	
//	static private final Method METHOD_TO_NON_EMPTY_STRING = 
//			Elemental.getMethod(MutexAssignedVersion.class, "toNonEmptyString", boolean.class);
	static private final Method METHOD_TO_Z3_SMT_STRING = 
			Elemental.getMethod(MutexAssignedVersion.class, "toZ3SmtString", boolean.class, boolean.class, boolean.class);
	
	
	
	/**
	 * Mutex assigned's
	 */
	private SortedSet<Assignable<PathVariable>> mas = null;
	private Expression conditional = null;

	/**
	 * Convenient constructor for {@link #negate()} ONLY.
	 * 
	 * @param lastWr
	 * @param condOrCe - constant condition or conditional expression
	 * @param role 
	 * @throws NoSuchVersionException 
	 */
	private MutexAssignedVersion(
			Assignable<PathVariable> lastWr, SortedSet<Assignable<PathVariable>> mas, 
			Expression condOrCe, FunctionallableRole role) throws NoSuchVersionException {
		super(lastWr, role);
		
		assert mas != null && condOrCe != null;
		this.mas = mas;
		conditional = condOrCe;
	}

	public static Version<? extends PathVariable> from(Assignable<PathVariable> asn) 
			throws ASTException, IncomparableException, 
			UncertainPlaceholderException, NoSuchVersionException {
		if (asn == null) throwNullArgumentException("assignable");
		return from(asn, asn.getPathVariablePlaceholder().getThreadRole());
	}
	
	/**<pre>
	 * Case Not-parent-cond-assigned:
	 * if (cond) {
	 * 	pasn = ...
	 * } else if (cond2) {
	 * 	asn = ...			// cond2 ? asn : asn.nextAssigned(), pmas = {pasn, ...}
	 * }
	 * 
	 * Case Not-parent-cond-not-assigned:
	 * ppasn = ...
	 * if (cond) {
	 * 	pasn = ...
	 * } else if (cond2) {
	 * 	... = ... asn ...	// from(ppasn) = from(asn.previousAssigned()) && asn.hasParentConditionOf(ppasn)
	 * }
	 * 
	 * Case Parent-cond-assigned:
	 * if (cond) {
	 * 	asn = ...			// cond ? asn : asn.nextAssigned()
	 * }
	 * 
	 * Case Parent-cond-not-assigned:
	 * if (cond) {
	 * 	ppasn = ...			// cond ? ppasn : ppasn.nextAssigned()
	 * 	if (cond2) {
	 * 		pasn = ...		// from(pasn) = cond && cond2 ? pasn : from(ppasn)
	 * 	}
	 * 	... = ... asn ...	// from(asn.previousAssigned()) = from(ppasn) && asn.hasParentConditionOf(ppasn) 
	 * }
	 * </pre>
	 * 
	 * @param asn
	 * @param role - TODO? excluding conditionally constant
	 * @return
	 */
	public static Version<? extends PathVariable> from(
			Assignable<PathVariable> asn, final FunctionallableRole role) 
					throws ASTException, NoSuchVersionException {
		if (asn == null) throwNullArgumentException("assignable");

		asn = asn.previousOrUnambiguousAssigned();
		if (!asn.hasMutexBranch()) 
			return throwNoSuchVersionException(asn, "having no mutex-branches");
		// loop initialized iterator may be constant
		if (asn.isLoopConditional()) 
			return throwNoSuchVersionException(asn, "loop-conditional should be functional");
		if (tests(asn.isConstant()) && testsNot(asn.isDirectlyConstant())) 
			return throwNoSuchVersionException(asn, "unconditional constant");								
		
		final NavigableSet<Assignable<PathVariable>> mas = asn.getMutexAssigneds();
		if (mas.isEmpty()) return throwNoSuchVersionException(asn, "not assigned");

		final Assignable<PathVariable> firstAsd = mas.first(), nextAsd = mas.higher(asn);
		// cond ? mas.lower(asn) : asn
		if (mas.size() == 1 
				|| (nextAsd == null && mas.lower(asn) == firstAsd)) {
			final Proposition firstCond = firstAsd.getBranchCondition();
			if (tests(()-> firstCond.isTrue())) return from(firstAsd, mas, firstCond, role);
			return throwNoSuchVersionException(asn, "not only one assigned");
		}

		// cond ? asn : mas.higher(asn)
		return from(asn, mas, 	
				ConditionalExpression.from(asn.getBranchCondition(), 
						asn.getDirectAssigner().get(0), 
						nextAsd.getDirectAssigner().get(0)), 
				role);
	}
	
	private static MutexAssignedVersion from(Assignable<PathVariable> asn, 
			SortedSet<Assignable<PathVariable>> mas, Expression condOrCe, 
			FunctionallableRole role) 
					throws NoSuchVersionException {
		if (condOrCe == null) throwNullArgumentException("condition");
		assert asn != null && mas != null && !mas.isEmpty() && role != null;
		
		return (MutexAssignedVersion) from(asn, role,
				()-> new MutexAssignedVersion(asn, mas, condOrCe, role));
//		if (cdv.conditionalExp != ce) cdv.conditionalExp = ce;
//		if (!cdv.getThreadRole().equals(role)) cdv.changeRole(role);
	}
	
//	/**
//	 * @param lastWritingReference 
//	 * - reference to wh[whi-1] | wh[whi-2] | ... | wh[whi-n] | const_1 | ... | const_m at right hand side 
//	 * of this delegate.
//	 * @param previousWritingReferences
//	 * @param role 
//	 * @throws NoSuchVersionException 
//	 */
//	public static Version<? extends PathVariable> from(Assignable lastWritingReference, 
//			SortedSet<Assignable> previousWritingReferences, ThreadRole role) throws NoSuchVersionException {
//		if (lastWritingReference == null) throwNullArgumentException("assignable");
//		
//		// checking (terminal) unconditional version
//		final List<IASTStatement> lastWrBranches = lastWritingReference.getBranchScopes();
//		if (lastWrBranches.isEmpty()) 	
//			return EnumeratedVersion.from(lastWritingReference.getPathVariable(), lastWritingReference, role);
//
//		// checking conditionally initialized version
//		final VODCondGen condGen = lastWritingReference.getCondGen();
//		final IASTNode lastWrBranch = lastWrBranches.get(0);
//		final Proposition cond = Proposition.fromParentBranchCondition(
//				lastWrBranch, lastWrBranch.getChildren()[0], null, condGen);
//		if (previousWritingReferences == null || previousWritingReferences.isEmpty()) 	
//			return from(lastWritingReference, previousWritingReferences, cond, role);
//		
//		final Assignable last2Wr = previousWritingReferences.last();
//		final List<IASTStatement> last2WrBranches = last2Wr.getBranchScopes();
//		if (!last2WrBranches.isEmpty() && last2WrBranches.get(0) instanceof IASTTranslationUnit)  
//				DebugElement.throwTodoException("unsupported conditional expression");
////				// independent branches, excluding if-else
////				(!ASTUtil.hasAncestorAs(lastWrBranch, last2WrBranch, last2WrBranches))
////				// including dependent (nested) branches
////				|| ASTUtil.dependsOnElseTo(lastWr.getTopNode(), last2Wr.getTopNode())) {
////		try {
//			
//		final PathVariablePlaceholder lastPvp = lastWritingReference.getPathVariablePlaceholder(),
//				last2Pvp = last2Wr.getPathVariablePlaceholder();
//		final SortedSet<Assignable> last3Wrs = previousWritingReferences.headSet(last2Wr);
//		final Expression e = ConditionalExpression.from(cond, lastPvp, last2Pvp);
//		if (e instanceof ConditionalExpression) try {
//			final ConditionalExpression ce = (ConditionalExpression) e;
//			last2Pvp.reversion(last3Wrs == null || last3Wrs.isEmpty()
//					? from(last2Wr, last3Wrs, (ConditionalExpression) ce.negate(), role)
//					: from(last2Wr, last3Wrs, role));
//			return from(lastWritingReference, previousWritingReferences, ce, role);
//		} catch (Exception ex) {
//			return throwUnhandledException(ex);
//		}
//		else if (e instanceof PathVariablePlaceholder) {
//			final PathVariablePlaceholder pvp = (PathVariablePlaceholder) e;
//			// unconditionally true version
//			if (pvp == lastPvp) return from(lastWritingReference, previousWritingReferences, cond, role);
//			// unconditionally false version
//			if (pvp == last2Pvp) return from(last2Wr, last3Wrs, role);
//			return pvp.getVersion(role);
//		}
//
////		} catch (Exception e) {
////			e.printStackTrace();
////		}
//		return throwTodoException("unsupported conditional version");
//	}



//	@Override
//	protected Expression cacheAssignerIf() {
//		return getAssigned();
//	}

	@Override
	protected Set<ArithmeticGuard> cacheArithmeticGuards() {
		assert conditional != null;
		return conditional.getArithmeticGuards();
	}
	
	@Override
	protected Boolean cacheConstant() {
		assert conditional != null && !mas.isEmpty();
		return false;	// conditional == null => isConstant
	}

	@Override
	protected Set<Function> cacheDirectFunctionReferences() {
		assert conditional != null;
		return conditional.getDirectFunctionReferences();
	}
	
	@Override
	protected void cacheDirectSideEffect() {
		assert conditional != null;
//		andSideEffect(super.cacheDirectSideEffect());	// path variable side-effect includes ALL placeholders' one
		andSideEffect(conditional.getSideEffect());	// path variable side-effect includes ALL placeholders' one
	}

	/**
	 * @return both itself and previous mutex-assigneds for variable-declaration use.
	 */
	@Override
	protected <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType) {
		assert conditional != null;
		final Set<T> dvrs = new HashSet<>(super.cacheDirectVariableReferences(refType));
		dvrs.addAll(conditional.getDirectVariableReferences(refType));
		return dvrs;
	}
	
	/* (non-Javadoc)
	 * @see ompca.condition.ConditionElement#getPointers()
	 */
	@Override
	public Set<Pointer> getPointers() {
		assert conditional != null;
		return conditional.getPointers();
	}
	
	

	/**
	 * @return non-null
	 */
	public Assignable<PathVariable> getLastAssigned() {
		assert mas != null;
		return mas.last();
	}
	
	@Override
	public NavigableSet<Assignable<?>> getAssigneds() {
		return new TreeSet<>(mas);
	}

	@Override
	protected ConditionElement cacheScope() {
		assert conditional != null;
		return conditional.getScope();
	}
	
//	public Type getType() {
//		assert conditional != null;
//		return conditional.getType();
//	}

	public PathVariablePlaceholder getLastPlaceholder() {
		return getLastAssigned().getPathVariablePlaceholder();
//			return isUnconditional() 
//					? getAssignable().getPathVariablePlaceholder()
//					// isConditional()
//					: (isConditionallyInitiallized() ? getAssignable() : mas.last())
//					.getPathVariablePlaceholder();
//					
	}
	
	public PathVariablePlaceholder previousPlaceholder() 
			throws IncomparableException {
		try {
			return (isConditionallyInitiallized() ? 
					getAssignable() : mas.first())
					.previous().getPathVariablePlaceholder();
			
		} catch (IncomparableException e) {
			throw e; 
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	
//	public Assignable previousRuntimeOf(Assignable asn) {
//	}
	


	@Override
	public Boolean dependsOn(Expression e) {
		assert conditional != null;
		return conditional.dependsOn(e);
	}

	/* (non-Javadoc)
	 * @see ompca.condition.ConditionElement#isEmpty()
	 */
	@Override
	public boolean isEmpty() {
		assert conditional != null;
		return conditional.isEmpty();
	}

	public boolean isConditionallyInitiallized() {
		return mas == null || mas.isEmpty();
	}
	
	public boolean isUnconditional() {
		return isUnconditionallyTrue() || isUnconditionallyFalse();
	}
	
	public boolean isUnconditionallyTrue() {
		assert conditional != null;
		return conditional instanceof Proposition 
				&& ((Proposition) conditional).isTrue();
	}
	
	public boolean isUnconditionallyFalse() {
		assert conditional != null;
		return conditional instanceof Proposition 
				&& ((Proposition) conditional).isFalse();
	}
	
//	public boolean isSubFirstFor(SerialFormat format) {
//		return true;
//	}

	protected boolean equalsToCache(SystemElement e2) {
		assert conditional != null;
		return conditional.equals(((MutexAssignedVersion) e2).conditional) 
				&& super.equalsToCache(e2);
	}
	
	protected List<Integer> hashCodeVars() {
		assert conditional != null;
		List<Integer> vars = new ArrayList<>(super.hashCodeVars());
		vars.add(conditional.hashCode());
		return vars;
	}
	

	
	/* (non-Javadoc)
	 * @see ompca.condition.Expression#negate()
	 */
	@Override
	public Expression negate() {
		assert conditional != null;
		return getTry(()-> new MutexAssignedVersion(
				getLastAssigned(), 
				mas, 
				(ConditionalExpression) conditional.negate(), 
				getThreadRole()),
				e-> throwTodoException(e));
	}

	
	
//	static public <T, Subject extends Referenceable> T throwNoSuchVersionException(
//			final VersionEnumerable<Subject> venum) throws NoSuchVersionException {
//		return throwNoSuchVersionException(venum, "not a conditionally assigned variable");
//	}


	
	@Override
	protected String toNonEmptyString(boolean usesParenthesesAlready) {
		return isUnconditionallyTrue() ? 
				// conditional expression is default at top-level
				super.toNonEmptyString(usesParenthesesAlready) : conditional.toString(); 	
//		try {
//			return guardReenter(
//					()-> conditional.toString(), 	// conditional expression is default at top-level
//					()-> super.toNonEmptyString(usesParenthesesAlready), 
//					METHOD_TO_NON_EMPTY_STRING);
//
//		} catch (Exception e) {
//			return throwUnhandledException(e);
//		}
	}
	
	/**
	 * Excluding duplicate platform variable/function declaration.
	 * @param decl
	 * @return empty string if already declared
	 */
	@Override
	public String toZ3SmtDeclaration(final String decl) {
		if (!MUTEX_DECLS.contains(decl)) {
			MUTEX_DECLS.add(decl);
			return decl;
		}
		return "";
	}

	/**
	 * @see ompca.condition.ConditionElement#toZ3SmtString()
	 */
	@SuppressWarnings("unchecked")
	@Override
	public String toZ3SmtString(boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs) {
		if (printsVariableDeclaration) {
			String decl = "";
			for (Version<Variable> v : getDirectVariableReferences(Version.class)) {
				final String subDecl = toZ3SmtDeclaration(equalsAssignable(v)
						? super.toZ3SmtString(true, printsFunctionDefinition, isLhs)		// default to print ID
						: debugGet(()-> v.toZ3SmtString(true, printsFunctionDefinition, isLhs)));
				if (!subDecl.isBlank()) decl += (subDecl + "\n");
			}
			return decl;
		}
		
		// printing conditional expression for non-variable-declaration  
		try {
		return isUnconditional()
				? super.toZ3SmtString(false, printsFunctionDefinition, isLhs) 				// default to print ID
				: guard(
						()-> conditional.toZ3SmtString(false, false, isLhs), 
						()-> super.toZ3SmtString(false, printsFunctionDefinition, isLhs), 	// default to print ID
						METHOD_TO_Z3_SMT_STRING);
				
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}

}