package ompca.vodcg.condition;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;

import org.eclipse.cdt.core.dom.IName;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTName;

import ompca.DuoKeyMap;
import ompca.condition.SerialFormat;
import ompca.vodcg.ASTAddressable;
import ompca.vodcg.ASTException;
import ompca.vodcg.ASTUtil;
import ompca.vodcg.Assignable;
import ompca.vodcg.SystemElement;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.data.ArithmeticGuard;
import ompca.vodcg.condition.data.PlatformType;
import ompca.vodcg.condition.data.Pointer;
import ompca.vodcg.condition.version.FunctionalVersion;
import ompca.vodcg.condition.version.FunctionallableRole;
import ompca.vodcg.condition.version.ThreadRoleMatchable;

/**
 * FunctionCall ::= IDRef '(' (Expression (',' Expression)*)? ')'
 * 
 * A relation-like function reference, where a function call relates its arguments
 * and call proposition (its direct side-effect).
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class FunctionCall<F extends Function>
// TODO? extends Relation
extends Reference<F> implements ArithmeticExpression {

	/**
	 * For readability in a complicated proposition, every function call 
	 * brings a company proposition place-holder which refers and carries 
	 * the side effect of the call. 
	 *
	 * TODO: The subject call stores the side effect as general expressions do.
	 */
	static public class CallProposition extends Proposition {

		private FunctionCall<?> call;

		protected CallProposition(FunctionCall<?> call) {
			this(call, null);
		}
		
		private CallProposition(FunctionCall<?> call, Supplier<Proposition> sideEffect) {
			super(	Operator.FunctionCall, 
					call.args != null ? 
							call.args : Collections.emptyList(),
					call.getScopeManager());	// later scope setting
			
			this.call = call;
			/*
			 * Meaning the subject boolean function is accessed and examined.
			 * TODO? default call proposition for a non-bool function: empty
			 * TODO? Backing up call's function scope because it will be replaced by the one of 
			 * call proposition, which is null before initialized, during adding operand. 
			 */
			andSideEffect(()-> BooleanFunction.from(call.getSubject(), 
					sideEffect != null ? sideEffect.get() : this));
			setFinal();
		}

		private Proposition getSideEffectAssertion() {
			return getSkipNull(()->
			getSideEffect().getPathCondition().getAssertion().get());
		}
		
		public FunctionCall<?> getCall() {
			return call;
		}
		
		public Function getCallFunction() {
			assert call != null;
			return call.getSubject();
		}
		
		@Override
		public String getIDSuffix(SerialFormat format) {
			assert call != null;
			return call.getIDSuffix(format);
		}
		
//		public Collection<? extends Expression> getOperands() {
//			assert call != null;
//			List<Expression> oprds = call.args;
//			return oprds == null 
//					? Collections.emptyList()
//					: Collections.unmodifiableList(oprds);
//		}
		
//		public Set<VOPConditions> getSideEffect() {
//			return Collections.singleton(new VOPConditions(null, new PathCondition(this)));
//		}
		
		@Override
		protected ConditionElement cacheScope() {
			return getCall().getScope();
		}
		
		@Override
		protected Function cacheFunctionScope() {
			return getCall().getFunctionScope();
		}
		
		@Override
		protected Set<Function> cacheDirectFunctionReferences() {
			assert call != null;
			return call.getDirectFunctionReferences();
		}
		
		@Override
		protected <OT extends Expression> boolean cacheOperandDirectSideEffect(
				final OT oprd) throws ClassCastException {
			assert call != null;
			for (Expression arg : call.getArguments())
				andSideEffect(()-> arg.getSideEffect());
			return false;
		}

		/* (non-Javadoc)
		 * @see ompca.vodcg.condition.ConditionElement#getVariableReferences()
		 */
		@Override
		protected <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType) {
			assert call != null;
			return call.cacheDirectVariableReferences(refType);
		}
		
		@Override
		protected Boolean cacheGlobal() {
			return call.isGlobal();
		}
		
		@Override
		public boolean isSemanticallyEmpty() {
			return getSideEffectAssertion() != this;
		}

		@Override
		public boolean suitsSideEffect() {return true;}
		
//		protected Proposition andByReduce(Proposition newProp) {
//			assert newProp != null;
//			Proposition callRelNew = getSubject()
//					.toSideEffectCall(Operator.And, newProp);
//			return callRelNew == null 
//					? super.andByReduce(newProp) : callRelNew;
//		}
//		
//		protected Proposition orByReduce(Proposition newProp) {
//			assert newProp != null;
//			Proposition callRelNew = getSubject()
//					.toSideEffectCall(Operator.Or, newProp);
//			return callRelNew == null 
//					? super.orByReduce(newProp) : callRelNew;
//		}
//		
//		protected Proposition implyByReduce(Proposition newProp) {
//			assert newProp != null;
//			Proposition callRelNew = getSubject()
//					.toSideEffectCall(Operator.Imply, newProp);
//			return callRelNew == null 
//					? super.implyByReduce(newProp) : callRelNew;
//		}
//		
//		protected Proposition iffByReduce(Proposition newProp) {
//			assert newProp != null;
//			Proposition callRelNew = getSubject()
//					.toSideEffectCall(Operator.Iff, newProp);
//			return callRelNew == null 
//					? super.iffByReduce(newProp) : callRelNew;
//		}


		
//		/* (non-Javadoc)
//		 * @see ompca.vodcg.condition.Proposition#reduceOnce()
//		 */
//		@Override
//		public Element reduceOnce() {
//			return call.reduceOnce();
//		}
		
		protected String toNonEmptyString(boolean usesParenAlready) {
			return call.toNonEmptyString(usesParenAlready);
		}
		
		/**
		 * @return true representing an invisible place-holder except its side-effects.
		 * @see ompca.vodcg.condition.Proposition#toZ3SmtString(boolean, boolean, boolean)
		 */
		@Override
		public String toZ3SmtString(
				boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs) {
//			return call.toZ3SmtString(false, false);
//			return True.from(getOp(), call).toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition);
			return isSemanticallyEmpty()
					? ""	// throwTodoException("recursive side-effect");
					: getSideEffectAssertion().toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition, isLhs);
		}

	}

	
	
//	private static final Method METHOD_CACHE_DIRECT_SIDE_EFFECT = 
//			Elemental.getMethod(FunctionCall.class, "cacheDirectSideEffect");

	/**
	 * Using linear maps to avoid FunctionalVersion.getArguments() during FunctionalVersion.super()
	 * via Function.hashCode()
	 */
	private static final 
	DuoKeyMap<Function, List<?>, FunctionCall<? extends Function>> 
	ALL_CALLS 			= new DuoKeyMap<>();
	

	
	final private List<Expression> args = new ArrayList<>();
	private CallProposition prop;
	
	/**
	 * @param f
	 * @param callName - null means a virtual call
	 * @param args
	 * @param scope
	 */
	@SuppressWarnings({ "unchecked" })
	protected FunctionCall(BooleanFunction f, 
			IName callName, final List<?> args, ConditionElement scope) {
		super((F) f, callName != null, initGlobal(callName, scope));
		init(new CallProposition((FunctionCall<BooleanFunction>) this), 
				callName, null, args, scope);
	}
	
	@SuppressWarnings("unchecked")
	protected FunctionCall(BooleanFunction f, 
			String callName, final List<?> args, ConditionElement scope) {
		super((F) f, false, initGlobal(scope));
		init(new CallProposition((FunctionCall<BooleanFunction>) this), 
				null, callName, args, scope);
	}
	
	/**
	 * @param f
	 * @param callName - null means a non-AST call
	 * @param args - ONLY in either IASTInitializerClause or Expression type
	 * @param scope
	 * @param sideEffect - attached side-effect, may be duplicate
	 */
	private FunctionCall(F f, IName callName, final List<?> args, 
			ConditionElement scope, Supplier<Proposition> sideEffect) 
			throws ASTException {
		super(f, callName != null, initGlobal(callName, scope));
		
		init(sideEffect == null ? null : new CallProposition(this, sideEffect), 
				callName, null, args, scope);
	}

	private FunctionCall(F f, 
			String callName, final List<?> args, ConditionElement scope) 
			throws ASTException {
		super(f, false, initGlobal(scope));
		
		init(null, null, callName, args, scope);
	}
	
//	public FunctionCall(Function f, IASTInitializerClause[] args, Set<Proposition> seProps) {
//		this(f, args, seProps);
//	}

	private static Boolean initGlobal(final ConditionElement scope) {
		return getSkipNull(()-> scope == null || scope.isGlobal());
	}
	
	private static Boolean initGlobal(IName callName, final ConditionElement scope) {
		return getSkipNull(()-> (callName != null && ASTUtil.isGlobal(callName))
				|| scope == null || scope.isGlobal());
	}
	
	private void init(final CallProposition cp, final IName cn, final String cn2, 
			final List<?> args, final ConditionElement scope) 
			throws ASTException {
		if (cn == null && cn2 == null) throwNullArgumentException("call name");
		if (scope == null) throwNullArgumentException("call scope");

		if (cn != null) setName(cn);
		if (cn2 != null) setName(cn2);
		if (args != null && !args.isEmpty()) {
			for (Object arg : args) {
				if (arg instanceof Expression) 
					this.args.add((Expression) arg);
				else if (arg instanceof IASTInitializerClause) 
					this.args.add(Expression.fromRecursively((IASTInitializerClause) arg, scope.cacheRuntimeAddress(), getCondGen()));
				else throwTodoException("unsupported arguments");
				
//				int index = 0;
//				
//				/* TODO? e.g. randlc(&tran, ...) 
//				 * -> tran = *x 
//				 * -> addSideEffect(newAndSubstitute(*x, tran))
//				 */
//				if (callsByReference(e)) {
//					Expression df = ((Pointer) e).getDepointFrom();
//					for (VOPConditions se : callee.getSideEffect()) prop.addSideEffect(
//							((VOPConditions) se.clone()).substitute(
//									callee.getParameter(index), df));
//				}
//				index++;
			} 
			
			// ignoring side-effect for functionally versioned path variable access 
			// Or-ing callee parameters' side-effect
			final Function callee = getSubject();
			for (int i = 0, pub = callee.getParameterSize(); i < args.size(); i++) try { 
				final int i_ = i;
				final Supplier<VODConditions> argise = ()-> this.args.get(i_).getSideEffect();
				if (i < pub) callee.getParameter(i).orSideEffect(argise);
				else callee.orSideEffect(argise);	// for variable arguments
			} catch (Exception e) {
				throwTodoException(e);
			}
		}
		
		setScope(()-> scope);
		prop = cp == null ? new CallProposition(this) : cp;
		prop.setScope(scope, getFunctionScope());
		setSideEffect(prop);
		checkCircularDependency();
	}



	private static FunctionCall<? extends Function> from(
			Function f, final List<?> args, Supplier<FunctionCall<?>> callSup) 
					throws ASTException {
		assert callSup != null;
		if (f == null) throwNullArgumentException("function");
		
		FunctionCall<? extends Function> fcall = ALL_CALLS.get(f, args);
		if (fcall == null) 
			ALL_CALLS.put(f, args, fcall = callSup.get());
		return fcall;
	}

	/**
	 * @param f
	 * @param args - ONLY in either IASTInitializerClause or Expression type
	 * @param scope - must be provided explicitly if args is null
	 * @param sideEffect 
	 * @return
	 */
	public static FunctionCall<? extends Function> from(Function f, 
			IName callName, final List<?> args, ConditionElement scope, 
			Supplier<Proposition> sideEffect) 
					throws ASTException {
		return from(f, args, 
				()-> new FunctionCall<>(f, callName, args, scope, sideEffect));
	}
	
	public static FunctionCall<? extends Function> from(
			Function f, String callName, final List<?> args, ConditionElement scope) 
					throws ASTException {
		return from(f, args, 
				()-> new FunctionCall<>(f, callName, args, scope));
	}
	
//	/**
//	 * @param fname
//	 * @param args
//	 * @param scope - must be provided explicitly if args is null
//	 * @param condGen 
//	 * @return
//	 * @throws CoreException
//	 * @throws InterruptedException
//	 */
//	public static FunctionCall<? extends Function> getCall(IName fname, 
//			IASTInitializerClause[] args, VOPCondGen condGen) 
//			throws CoreException, InterruptedException {
//		return getCall(
//				get(fname, (IFunction) null, condGen), 
//				args, 
//				getFunctionScopeOf(fname, condGen));
//	}
//
//	/**
//	 * @param fname
//	 * @param args
//	 * @param scope - must be provided explicitly if args is null
//	 * @param condGen 
//	 * @return
//	 * @throws CoreException
//	 * @throws InterruptedException
//	 */
//	public static FunctionCall<? extends Function> getCall(IName fname, 
//			Expression[] args, VOPCondGen condGen) 
//			throws CoreException, InterruptedException {
//		return getCall(
//				get(fname, (IFunction) null, condGen), 
//				args, 
//				getFunctionScopeOf(fname, condGen));
//	}
	
	/**
	 * For functionally version-ed array path variables.
	 * 
	 * @param fv
	 * @param sideEffect
	 * @return
	 */
	public static FunctionCall<? extends Function> from(
			FunctionalVersion fv, Supplier<Proposition> sideEffect) {
		if (fv == null) return throwNullArgumentException("array access version");
		
		return from(
				Function.from(fv), 
				fv.getIName(), 
				fv.getArguments(), 
				fv.getScope(), 
				sideEffect);
	}
	
	public static FunctionCall<? extends Function> fromRecursively(
			IASTFunctionCallExpression exp, Supplier<Proposition> sideEffect, final ASTAddressable rtAddr, 
			VODCondGen condGen) 
					throws ASTException {
		if (exp == null) throwNullArgumentException("expression");

		final IASTName fName = ASTUtil.getNameOf(exp);
		if (fName == null) throwTodoException("unsupported function call");

		return from(Function.from(ASTUtil.getFunctionBindingOf(fName), rtAddr, condGen), 
				fName,
				Arrays.asList(exp.getArguments()),
				Function.getFunctionScopeOf(exp, rtAddr, condGen), 
				sideEffect);
	}


	
	protected void checkCircularDependency() {
		Function caller = getCaller();
		if (caller == null) return;
		
		Function callee = getSubject();
		if (caller.isGround() && callee.isInAST()) 
			Function.throwImcomparableException(caller, callee, "non-existent calling");

		Set<Function> calleeRefs = callee.getFunctionReferences(null);
		// TODO: replaced by Forall x, x > n /\ caller(x, ...) -> callee(x, ...) 
		if (calleeRefs != null && calleeRefs.contains(caller)) 
			Function.throwImcomparableException(caller, callee, "mutual inclusion");
	}
	
//	final static private Method METHOD_EXPRESSION_TRAVERSAL = 
//			getMethod(FunctionCall.class, "initiatesExpressionTraversal");
//	/* (non-Javadoc)
//	 * @see ompca.vodcg.condition.ArithmeticExpression#initiatesExpressionTraversal()
//	 */
//	@Override
//	public boolean initiatesExpressionComputation() {
//		return initiatesElementalTraversal(METHOD_EXPRESSION_TRAVERSAL);
//	}
//
//	/* (non-Javadoc)
//	 * @see ompca.vodcg.condition.ArithmeticExpression#initiateExpressionTraversal()
//	 */
//	@Override
//	public void initiateExpressionComputation() {
//		initiateElementalTraversal(METHOD_EXPRESSION_TRAVERSAL);
//	}
//
//	/* (non-Javadoc)
//	 * @see ompca.vodcg.condition.ArithmeticExpression#resetExpressionTraversal()
//	 */
//	@Override
//	public void resetExpressionComputation() {
//		resetElementalTraversal(METHOD_EXPRESSION_TRAVERSAL);
//	}
	

	
	public List<Expression> getArguments() {
		return args == null ? Collections.emptyList() : args;
	}
	
	/**
	 * @param index
	 * @return
	 */
	public Expression getArgument(int index) {
		if (args == null || index < 0 || index >= args.size()) return null;
		return args.get(index);
	}
	
	public int getArgumentIndex(Assignable<?> arg) {
		if (arg != null && args != null && !args.isEmpty()) try {
			final PathVariablePlaceholder pvd = arg.getPathVariablePlaceholder();
			final int size = args.size();
			for (int idx = 0; idx < size; idx++) 
				if (tests(args.get(idx).dependsOn(pvd))) return idx;
			
		} catch (Exception e) {
			throwTodoException(e);
		}
		return -1;
	}
	
	public VariablePlaceholder<?> getParameter(Assignable<?> arg) {
		if (arg == null) throwNullArgumentException("argument");
		try {
			final VariablePlaceholder<?> p = 
					getSubject().getParameter(getArgumentIndex(arg));
			if (isVararg(arg)) p.setType(arg.getType());
			return p;
			
		} catch (IndexOutOfBoundsException e) {
			return throwUnhandledException(e);
		}
	}

	public PathVariablePlaceholder getTopPlaceholder() {
		return Assignable.from(getASTName(), cacheRuntimeAddress(), getCondGen())
				.getPathVariablePlaceholder();
	}

	public Function getCaller() {
//		assert getFunctionScope() != null after parsing done
		return getFunctionScope();
	}

	public Function getCallee() {
		return getSubject();
	}
	
	public CallProposition getCallProposition() {
		return prop;
	}

	/**<pre>
	 * Default scope hierarchy:
	 * 
	 * 1) Expression -> SideEffect
	 * 2) Function -> Proposition -> FunctionCall -> CallProposition
	 * </pre>
	 * @see ompca.vodcg.condition.Reference#getScope()
	 */
	@Override
	protected ConditionElement cacheScope() {
		if (args != null && !args.isEmpty()) {
			ConditionElement scope = null;
			for (Expression arg : args) {
				scope = getCommonScope(scope, arg.getScope());	// TODO: \/ arg.scope
//				if (scope != null) break;
			}
		}
		return null;
	}
	
	@Override
	protected <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType) {
		final Set<T> vrs = new HashSet<>();
		if (args != null) for (Expression arg : args) {
			@SuppressWarnings("unchecked")
			final Set<T> argVrs = (Set<T>) 
					arg.cacheDirectVariableReferences(refType);
			if (argVrs != null) vrs.addAll(argVrs);
		}
		return vrs;
	}
	
	@Override
	public Set<Pointer> getPointers() {
		Set<Pointer> ps = new HashSet<>();
		if (args != null) for (Expression arg : args) {
			Set<Pointer> argPs = arg.getPointers();
			if (argPs != null) ps.addAll(argPs);
		}
		return ps;
	}

	/**
	 * @return TODO? body expression with arguments involved
	 */
	public Expression getReturn() {
		return getSubject().getBody();
//		TODO? return getSubject().getBody().replace(getArguments());
	}
	
	public ArithmeticExpression getReturnArithmetic() {
		try {
			return (ArithmeticExpression) getReturn();
			
		} catch (ClassCastException e) {
			return throwUnhandledException(e);
		}
	}
	
	@Override
	public FunctionallableRole getThreadRole() {
		return get(()-> super.getThreadRole(),
				()-> ThreadRoleMatchable.getThreadRole(getArguments()));
	}

	@Override
	public PlatformType getType() {
		return getSubject().getType();
	}
	
	@Override
	protected Set<ArithmeticGuard> cacheArithmeticGuards() {
		Set<ArithmeticGuard> ags = new HashSet<>(getSubject().getArithmeticGuards());	
		if (args != null) for (Expression arg : args) {
			if (arg == null) throwNullArgumentException("argument");
			if (arg == this) throwTodoException("recursive call");
			addAllSkipException(ags, ()-> arg.getArithmeticGuards());
		}
		return ags;
	}
	
	@Override
	protected void cacheDirectSideEffect() {
//		if (enters(METHOD_CACHE_DIRECT_SIDE_EFFECT)) return null;
//		
//		enter(METHOD_CACHE_DIRECT_SIDE_EFFECT);
		// root side-effect
		andSideEffect(()-> prop);
		
		// leaf side-effect
		if (args != null) for (Expression arg : args) {
			if (arg == null) throwNullArgumentException("argument");
			if (arg == this) throwTodoException("recursive call");
			andSideEffect(()-> arg.getSideEffect());
		}
//		leave(METHOD_CACHE_DIRECT_SIDE_EFFECT);
	}
	
	protected Set<Function> cacheDirectFunctionReferences() {
		Set<Function> refs = new HashSet<>();
		
		refs.add(getSubject());
		if (args != null) for (Expression arg : args) {
			Set<Function> subRefs = arg.getDirectFunctionReferences();
			if (subRefs != null) refs.addAll(subRefs);	// refs != subRefs
		}
		
		return refs;
	}

	@Override
	protected Boolean cacheGlobal() {
		return false;
	}
	
	@Override
	protected Boolean cacheConstant() {
		return args == null || args.isEmpty();
	}
	
	@Override
	protected FunctionCall<F> toConstantIf() {
		return this;
	}
	

	
	public boolean callsByReference(Expression arg) {
		return arg != null && args != null && args.contains(arg) 
				&& arg instanceof Pointer 
				&& ((Pointer) arg).getOp() == Pointer.Operator.Depoint;
	}
	
	
	
	/* (non-Javadoc)
	 * @see ompca.vodcg.condition.Expression#containsArithmetic()
	 */
	@Override
	public boolean containsArithmetic() {
		if (args != null) for (Expression arg : args) 
			if (arg.containsArithmetic()) return true;
		return false;
	}
	
	@Override
	public Boolean isZero() 
			throws ASTException {
		return getSkipNull(()-> getReturnArithmetic().isZero());
	}
	
	@Override
	public Boolean isPositive() {
		return getSkipNull(()-> getReturnArithmetic().isPositive());
	}
	
	@Override
	public Boolean isPositiveInfinity() {
		return getSkipNull(()-> getReturnArithmetic().isPositiveInfinity());
	}
	
	@Override
	public Boolean isNegative() {
		return getSkipNull(()-> getReturnArithmetic().isNegative());
	}
	
	@Override
	public Boolean isNegativeInfinity() {
		return getSkipNull(()-> getReturnArithmetic().isNegativeInfinity());
	}

	

	public boolean isVararg(Assignable<?> arg) {
		final Function f = getSubject();
		return f.hasVarargs() 
				&& getArgumentIndex(arg) >= f.getParameterSize() - 1;
	}
	
	@Override
	protected boolean equalsToCache(SystemElement e2) {
		FunctionCall<?> fc2 = (FunctionCall<?>) e2;
		return getSubject().getID((SerialFormat) null)
				.equals(fc2.getSubject().getID((SerialFormat) null)) &&
				(args == null ? fc2.args == null : args.equals(fc2.args));
	}
	
	@Override
	protected List<Integer> hashCodeVars() {
		return Arrays.asList(getSubject().hashCode(), 
				args == null ? 0 : args.hashCode());
	}

	
	
	@Override
	public boolean suitsSideEffect() {return true;}
	

	
	/* (non-Javadoc)
	 * @see ompca.vodcg.condition.Expression#negate()
	 */
	@Override
	public Expression negate() {
//		throwTodoException("unsupported negation");
		return ArithmeticExpression.super.negate();
	}


	
//	@Override
//	public Proposition toProposition() {
//		return getCallProposition();
//	}

	
	
	@Override
	public String toNonEmptyString(boolean usesParenthesesAlready) {
		String str = getSubject().getName() + "(";
		if (args != null && !args.isEmpty()) {
			for (Expression arg : args) 
				str += (arg.toNonEmptyString(usesParenthesesAlready) + ", ");
			str = str.substring(0, str.length() - 2);
		}
		return str + ")";
	}
	

	
	@Override
	public String toZ3SmtString(boolean printsVariableDeclaration, 
			boolean printsFunctionDefinition, boolean isLhs) {
		return debugGet(()->
		Relation.toZ3SmtString(getSubject().getName(), args));
	}

}