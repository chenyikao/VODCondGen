package ompca.vodcg.condition;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

import org.eclipse.cdt.core.dom.IName;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTReturnStatement;
import org.eclipse.cdt.core.dom.ast.IASTStandardFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IBinding;
import org.eclipse.cdt.core.dom.ast.IFunction;
import org.eclipse.cdt.core.dom.ast.IParameter;

import ompca.DuoKeyMap;
import ompca.Elemental;
import ompca.condition.SerialFormat;
import ompca.vodcg.ASTAddressable;
import ompca.vodcg.ASTException;
import ompca.vodcg.ASTUtil;
import ompca.vodcg.Assignable;
import ompca.vodcg.IncomparableException;
import ompca.vodcg.SystemElement;
import ompca.vodcg.UncertainPlaceholderException;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.FunctionCall.CallProposition;
import ompca.vodcg.condition.Relation.Operator;
import ompca.vodcg.condition.data.ArithmeticGuard;
import ompca.vodcg.condition.data.ArrayType;
import ompca.vodcg.condition.data.DataType;
import ompca.vodcg.condition.data.NumericExpression;
import ompca.vodcg.condition.data.PlatformType;
import ompca.vodcg.condition.data.Pointer;
import ompca.vodcg.condition.data.PointerType;
import ompca.vodcg.condition.version.ArrayAccessVersion;
import ompca.vodcg.condition.version.FunctionallableRole;
import ompca.vodcg.condition.version.NoSuchVersionException;
import ompca.vodcg.condition.version.ThreadRoleMatchable;

/**
 * Function ::= Return? ID '(' (Variable (',' Variable)*)? ')' 
 * 				'(' (Arithmetic '->' Predicate) | And | Expression ')' 
 * 
 * A function is ONLY an encapsulation of partial VOP but NO whole C/C++ program code mapping.
 * 
 * A function in default has a global scope.
 * 
 * TODO: extends {@link Relation} as functional relation
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class Function 
extends Referenceable 
implements SideEffectElement, Comparator<Function>, Comparable<Function> {
	
	static public class Parameter extends ompca.Parameter {
		public Parameter(String name, PlatformType type) {
			super(name, type);
		}
		
		static public Parameter[] from(
				final List<? extends Expression> args) {
			if (args == null || args.isEmpty()) return null;
			
			final List<Parameter> argList = new ArrayList<>();
			int i = 1;
			for (Expression arg : args) argList.add(new Parameter(
					getDefaultName(i++), arg.getType()));
			return argList.toArray(new Parameter[] {});
		}
		
	}
	
	static public enum Comparison {
		/**
		 * is called before
		 */
		isBefore, 
		
		equals, 
		
		/**
		 * is called after
		 */
		isAfter;
	}


	
	private static final Method METHOD_SET_BODY = 
			Elemental.getMethod(Function.class, "setBody", Expression.class);
	private static final Method METHOD_TRAVERSAL_OF = 
			Elemental.getMethod(Function.class, "initiateTraversalOf");

	private static final Map<IBinding, Function> C_FUNCTIONS 				= new HashMap<>();
	private static final DuoKeyMap<String, String, Function> LIB_FUNCTIONS 	= new DuoKeyMap<>();
	
	private static final Set<Function> STRUCTURAL_TRAVERSED_FUNCTIONS 		= new HashSet<>();
	private static final Map<String, String> TYPE_BODY_CACHE				= new HashMap<>();


	
	private static final 
	DuoKeyMap<Function, Function, Integer> 	// ordered keys
	COMPARE_RESULTS		= new DuoKeyMap<>();
	
//	private static int MaxGroundDifference = 0;

	private final Set<Function> circularIndependentFunctions = new HashSet<>();
	
	
	
	private String library = null;

	private Supplier<List<VariablePlaceholder<?>>> paramsSup = null;
	private Expression body = null;
	
//	private Boolean isInAST = null;

//	private SortedSet<Function> frsCache = null;

//	private Set<Function>	calledFuncs = new HashSet<>();
	
	
	
	/**
	 * Constructor for global non-AST (general) functions. 
	 * 
	 * @param library
	 * @param name
	 * @param type 
	 * @param condGen
	 */
	protected Function(
			String library, String name, PlatformType type, VODCondGen condGen) {
		super(name, type, condGen);
		
		this.library = library;
		setNonAST();
		setGlobal();
	}
	
	/**
	 * Constructor for AST array-access-version-placeholder-based 
	 * functional-variable functions. 
	 * 
	 * @param aav
	 */
	private Function(ArrayAccessVersion<?> aav) {
		super(aav.getASTName(), aav.getCodomainType(), aav.getRuntimeAddress(), aav.getCondGen());
		
		assert !(aav.getASTName().resolveBinding() instanceof IFunction);
		
		setName(aav.getID(null));	// named by version ID, as part of the function ID
		setParameters(()-> Parameter.from(
				NumericExpression.toExpressionList(aav.getNonSelfArguments())));
		setNonAST();
//		setGlobal();
	}
	
//	/**
//	 * Constructor for external/library C/C++ functions. 
//	 * 
//	 * @param name 
//	 * @param condGen 
//	 */
//	private Function(IName name, VODCondGen condGen) {
//		this(name, ASTUtil.getFunctionBindingOf(name), condGen);
//
//		isInAST = false;
//		setGlobal();
//	}

	/**
	 * Convenient internal factory method given redundant but pre-cached function binding.
	 * 
	 * @param fName
	 * @param fBinding
	 * @param condGen
	 */
	private Function(IName fName, IFunction fBinding, final ASTAddressable rtAddr, VODCondGen condGen) {
		this(fName, fBinding, ASTUtil.getDefinitionOf(fBinding), rtAddr, condGen);
//		
//		assert fName != null;
//		
//		// fBinding == null if f is a pseudo function
//		if (fBinding != null) setParameters(fBinding);
	}

	/**
	 * TODO? Function body is set later on demand of function calls.
	 * 
	 * @param cName
	 * @param definition
	 * @param condGen
	 */
	private Function(IName cName, IFunction cBinding, 
			IASTFunctionDefinition definition, final ASTAddressable rtAddr, VODCondGen condGen) {
		super(cName, cBinding, rtAddr, condGen);
		
		assert cName != null && cBinding != null && definition != null; 
//		throw new NullPointerException("AST function definition is required!");
		setParameters(definition);
	}



	protected void initiateTraversalOf() {
		STRUCTURAL_TRAVERSED_FUNCTIONS.add(this);
		enter(METHOD_TRAVERSAL_OF);
	}
	
	protected boolean initiatesTraversalOf() {
		return STRUCTURAL_TRAVERSED_FUNCTIONS.contains(this) 
				&& enters(METHOD_TRAVERSAL_OF);
	}
	
	protected void resetTraversalOf() {
		STRUCTURAL_TRAVERSED_FUNCTIONS.remove(this);
		leave(METHOD_TRAVERSAL_OF);
	}
	
//	public Collection<Function> collectFunctions() {
//		VOPConditions conds, f = getCachedFunctionOf(arg);
//		if (f == null) {
//			setCachedFunctionOf(arg, f = new Function(arg));
//			conds.and(f);
//		}
//		return conds.and(new FunctionCall(f, arg));
//	}
	


	public static Function from(
			IFunction cBinding, final ASTAddressable rtAddr, VODCondGen condGen) throws ASTException {
		return from(
				cBinding, 
				ASTUtil.getDefinitionOf(cBinding),
				rtAddr,
				condGen);
//		return Elemental.apply(
//				cName-> from(cName, cBinding, condGen),
//				()-> ASTUtil.getNameOf(ASTUtil.getDefinitionOf(cBinding)),
//				e-> ASTUtil.throwASTException(cBinding, e));
	}

	public static Function from(
			IASTFunctionDefinition definition, final ASTAddressable rtAddr, VODCondGen condGen) {
		if (definition == null || condGen == null) return null;
		return from(ASTUtil.getNameOf(definition), definition, rtAddr, condGen);
	}
	
	public static Function from(
			IASTFunctionCallExpression call, final ASTAddressable rtAddr, VODCondGen condGen) 
					throws ASTException {
		if (call == null || condGen == null) return null;
		final IBinding bind = ASTUtil.getNameOf(
				call.getFunctionNameExpression()).resolveBinding();
		return bind instanceof IFunction
				? from((IFunction) bind, rtAddr, condGen)
				: throwTodoException("unsupported call");
	}
	
	/**
	 * @param aav - is supposed with a location (either AST or index) 
	 * 	aware function name
	 * @return a location aware virtual function
	 * @throws ASTException
	 */
	public static Function from(ArrayAccessVersion<?> aav) 
			throws ASTException {
		if (aav == null) return throwNullArgumentException("array access version");

		final IASTName cName = aav.getASTName();
		final IBinding cBinding = cName.resolveBinding();
		if (cBinding == null) throwTodoException("AST function definition is required!");
		if (cBinding instanceof IFunction) throwTodoException("call other factory methods for IFunction");

		Function f = C_FUNCTIONS.get(cBinding);
		if (f == null) C_FUNCTIONS.put(cBinding, f = new Function(aav));
		return f;
	}
	
	public static Function from(
			IName cName, IASTFunctionDefinition definition, final ASTAddressable rtAddr, VODCondGen condGen) {
		return from(cName, null, definition, rtAddr, condGen);
	}
	
	public static Function from(
			IName cName, IFunction cBinding, final ASTAddressable rtAddr, VODCondGen condGen) 
					throws ASTException {
		return from(cName, cBinding, ASTUtil.getDefinitionOf(cBinding), rtAddr, condGen);
	}
	
	public static Function from(
			IFunction cBinding, IASTFunctionDefinition definition, final ASTAddressable rtAddr, VODCondGen condGen) 
			throws ASTException {
		return from(ASTUtil.getNameOf(definition), cBinding, definition, rtAddr, condGen);
	}
	
	public static Function from(
			String library, String name, PlatformType type, VODCondGen condGen, Parameter... params) {
		if (library == null) throwNullArgumentException("library");
		if (name == null) throwNullArgumentException("name");
		if (type == null) throwNullArgumentException("type");

		final String signature = getID(name, params);
		Function f = LIB_FUNCTIONS.get(library, signature);
		if (f == null) {
			LIB_FUNCTIONS.put(
					library, signature, f = new Function(library, name, type, condGen));
			f.setParameters(()-> params);
		}
		return f;
	}
	
	/**
	 * Convenient internal factory method given redundant but pre-cached function binding and definition.
	 * 
	 * @param cName - should be a function definition name instead of a function call name
	 * @param cBinding
	 * @param condGen 
	 * @return
	 */
	private static Function from(IName cName, IFunction fBinding, 
			IASTFunctionDefinition definition, final ASTAddressable rtAddr, VODCondGen condGen) 
					throws ASTException {
//		C_FUNCTIONS.clear();
		Function f = C_FUNCTIONS.get(fBinding);
		if (f != null) return f;
		
		// matching - library functions
		if (fBinding != null) {
			final String fid = getID(fBinding);
			f = VODCondGen.getCLibraryFunction(fid);
			if (f == null) for (Map<String, Function> idfMap 
					: LIB_FUNCTIONS.toMap().values()) {
				f = idfMap.get(fid);
				if (f != null) break;
			}
		} 
		
		if (f == null && cName == null) {
			condGen.log(null, fBinding + " is a non-library function");
			ASTUtil.throwASTException(fBinding, null);	
		}
		
		// matching - functions under construction
		if (f == null) for (Function tf : STRUCTURAL_TRAVERSED_FUNCTIONS) 
			if (ASTUtil.equals(tf.getIName(), cName, true)) {
				f = tf;
				break;
			}
		// matching - functions constructed
//		if (f == null) for (IName rName : C_FUNCTIONS.keySet()) 
//			if (ASTUtil.equals(rName, cName, true)) {
//				f = C_FUNCTIONS.get(rName);
//				break;
//			}

		// creating - set function body first if there's any body
		if (f == null) {
			if (cName instanceof IASTName) {
				final IASTName astName = (IASTName) cName;
				if (ASTUtil.getEnclosingFunctionCallOf(astName) != null)
					throwInvalidityException("function name instead of call name should be provided");
				assert astName.resolveBinding() instanceof IFunction;
			}
			
			if (fBinding != null) 
				f = new Function(cName, fBinding, rtAddr, condGen);
			else if (definition != null) {
				fBinding = ASTUtil.getFunctionBindingOf(cName);
				f = new Function(cName, fBinding, definition, rtAddr, condGen);
			} else 
				throwTodoException("non-C function");
//				f = new Function(cName, condGen);
		}
		
		C_FUNCTIONS.put(fBinding, f);
		return f;
	}

	/**
	 * @return All registered C/C++ functions.
	 */
	public static Set<Function> getCOnes() {
		return new HashSet<>(C_FUNCTIONS.values());
//		Set<Function> cfs = new HashSet<>();
//		for (Function cf : C_FUNCTION_REGISTRY.values()) if (!cfs.contains(cf)) cfs.add(cf);
//		return cfs;
	}
	
//	public static BooleanFunction getBooleanOne(IName fname, VOPCondGen condGen) {
//		Function f = get(fname, (IFunction) null, condGen);
//		if (f != null) {
//			if (f instanceof BooleanFunction) return (BooleanFunction) f;
//			if (f.getType() == DataType.Bool) return BooleanFunction.get(f, null);
//		}
//		return null;
//	}

	
	
	/**
	 * @param args - null means no arguments (for constant function calls)
	 * @param scope
	 * @return
	 */
	public FunctionCall<? extends Function> getCall(
			List<?> args, ConditionElement scope) {
		return FunctionCall.from(
				this, 
				getName(), 
				args, 
				scope);
	}
	
	/**
	 * @param callName
	 * @param args - null means no arguments (for constant function calls)
	 * @param scope
	 * @param sideEffect
	 * @return
	 */
	public FunctionCall<? extends Function> getCall(IName callName, 
			List<?> args, ConditionElement scope, Supplier<Proposition> sideEffect) {
		return FunctionCall.from(
				this, 
				callName, 
				args, 
				scope, 
				sideEffect);
	}
	
	
	
	/**
	 * A callee/caller is a function call instance, while here we care <em>only</em> 
	 * types of all callees.
	 * 
	 * TODO? including indirectly called ones?
	 * 
	 * @return
	 */
	public Set<Function> getCalledOnes() {
		return getFunctionReferences(null);
	}
	


	/**
	 * @param node
	 * @param condGen 
	 * @return
	 */
	public static Function getFunctionScopeOf(IASTNode node, final ASTAddressable rtAddr, VODCondGen condGen) {
		if (node == null) throwNullArgumentException("AST node");
		if (condGen == null) throwNullArgumentException("scope manager");
		return from(ASTUtil.getWritingFunctionDefinitionOf(node), rtAddr, condGen);
	}

	

	public String getLibrary() {
		return library;
	}
	
//	public List<Assignable> getAssignables(Assignable arg) {
//		if (arg == null) throwNullArgumentException("argument");
//		final Assignable param = getParameter(arg)
//		return Assignable.fromOf();
//	}

	public VariablePlaceholder<?> getParameter(int index) 
			throws IndexOutOfBoundsException {
		try {
			return getParameters().get(index);
			
		} catch (IndexOutOfBoundsException e) {
			final int last = getParameterSize() - 1;
			if (index >= last) {
				final VariablePlaceholder<?> lp = getParameter(last);
				if (lp.isVarargs()) {
					final String lpn = lp.getName();
					final VariablePlaceholder<?> vararg = 
							VariablePlaceholder.fromNonAST(Variable.fromNonAST(
									lpn.substring(0, lpn.length() - 1),	// _Varargs => _Vararg
									((ArrayType) lp.getType()).getType(), 
									true, ()-> this, null, getCondGen()), true);
					vararg.setAssigned(lp.isAssigned());
					return vararg;
				}
			}
			throw e;
		}
	}
	
	public VariablePlaceholder<?> getParameter(Assignable<?> param) {
		try {
			return getParameter(getParameterIndex(param));
			
		} catch (IndexOutOfBoundsException e) {
			return throwNullArgumentException(null, null, e);
		}
	}
	
	/**
	 * @return a non-null list
	 */
	public List<VariablePlaceholder<?>> getParameters() {
		return paramsSup != null 
				? paramsSup.get() 
				: Collections.emptyList();
	}
	
	public int getParameterSize() {
		return getParameters().size(); 
	}
	
	/**
	 * @param param - assignable to be checked if exists in any parameter
	 * @return
	 */
	public int getParameterIndex(Assignable<?> param) {
		if (param == null) throwNullArgumentException("assignable");
		return getParameterIndex(param.getPathVariablePlaceholder());
	}
	
	public int getParameterIndex(PathVariablePlaceholder pvp) {
//		if (pvp == null) throwNullArgumentException("path variable placeholder");
		if (pvp != null && pvp.getVariable().isParameter()) {
			for (int i = 0; i < getParameterSize(); i++) {
				VariablePlaceholder<?> p = getParameter(i);
				if (p instanceof PathVariablePlaceholder 
						&& pvp == (PathVariablePlaceholder) p) return i;
			}
		}
		return -1;
	}
	
	private void setParameters(Supplier<Parameter[]> params) {
//		initParameters();
		
		if (params == null) return;
		
		paramsSup = ()-> {
			final List<VariablePlaceholder<?>> ps = new ArrayList<>();
			for (Parameter p : getNonNull(()-> params.get())) {
				addParameter(ps, VariablePlaceholder.fromNonAST(
						p.getPeer1(), (PlatformType) p.getPeer2(), true, false, ()-> this, null, getCondGen()));
				// not assigned in body as default, TODO? including assigned by argument
			}
			return ps;
		};
	}
	
	/**
	 * For AST functions with definitions available.
	 * 
	 * @param f
	 */
	private void setParameters(IASTFunctionDefinition f) {
		initParameters();
		
		assert f != null;
		final IASTFunctionDeclarator fd = f.getDeclarator();
		if (fd instanceof IASTStandardFunctionDeclarator) {
			final IASTParameterDeclaration[] fParams = 
					((IASTStandardFunctionDeclarator) fd).getParameters();
			if (fParams != null) for (IASTParameterDeclaration fp : fParams) try {
				final VariablePlaceholder<?> p = PathVariablePlaceholder.from(
						fp.getDeclarator(), getRuntimeAddress(), getCondGen());
				if (p == null) throwTodoException("Null parameter!");
				addParameter(p);
				
			} catch (UncertainPlaceholderException | ASTException 
					| IncomparableException | NoSuchVersionException e) {
				throwTodoException(e);
			}
		}
	}
	
//	/**
//	 * For the external/library functions with {@link IBinding} only.
//	 * 
//	 * @param f
//	 */
//	private void setParameters(IFunction f) {
//		final IASTFunctionDefinition fd = ASTUtil.getDefinitionOf(f);
//		if (fd != null) setParameters(fd);
//		else {	// for library functions
//			assert f != null;
//			final VODCondGen cg = getCondGen();
//			initParameters();
//			IParameter[] fParams = f.getParameters();
//			if (fParams != null) for (IParameter fp : fParams) try {
//				VariablePlaceholder<?> p = PathVariablePlaceholder.from(fp, this, cg);
//				if (p == null) throwTodoException("Null parameter!");
//				paramsSup.add(p);
//				
//			} catch (UncertainPlaceholderException | ASTException | IncomparableException | NoSuchVersionException e) {
//				throwTodoException(e);
//			}
//		}
//	}
	
	private void addParameter(VariablePlaceholder<?> param) {
		addParameter(getParameters(), param);
	}
	
	private void addParameter(final List<VariablePlaceholder<?>> params, final VariablePlaceholder<?> param) {
		assert params != null && param != null;
		params.add(param);
		param.setFunctionScope(()-> this);
		paramsSup = ()-> params;
	}
	
	private void initParameters() {
		paramsSup = ()-> new ArrayList<>();
//		if (paramsSup == null) paramsSup = new ArrayList<>();
//		else if (!paramsSup.isEmpty()) paramsSup.clear();
	}

//	/**
//	 * For non-path functions.
//	 * 
//	 * @throws CoreException
//	 * @throws InterruptedException
//	 */
//	private void setParameters() throws CoreException, InterruptedException {
//		if (!paramsSup.isEmpty()) paramsSup.clear();
//		for (IParameter param : f.getParameters()) 
//			paramsSup.add(Variable.get(param, this, condGen));
//	}
	
	
	
	/**
	 * @return the body
	 */
	public Expression getBody() {
		if (body == null && !getType().equals(DataType.Void) && isInAST()) {
			// setting function body on demand
			setBody(getBody(ASTUtil.getDescendantsOfAs(
					ASTUtil.getWritingFunctionDefinitionOf(getASTName()).getBody(), 
					IASTReturnStatement.class).iterator()));

			if (body == null) throwTodoException("non-void return asked of empty body");
//			body = VariablePlaceholder.fromNonAST(getName() + "_return", 
//					getType(), false, this, null, getCondGen());
		}
		return body;
	}

	private Expression getBody(final Iterator<IASTReturnStatement> rit) {
		assert rit != null;
		if (!rit.hasNext()) return null;
		
		final VODCondGen cg = getCondGen();
		final IASTReturnStatement r = rit.next();
		
		initiateTraversalOf();
		final Proposition rcond = Proposition.fromParentBranchCondition(r, null, cg);
		final Expression ra = Expression.fromRecursively(r.getReturnArgument(), getRuntimeAddress(), cg),
				re = rcond == null ? ra : ConditionalExpression.from(rcond, ra, getBody(rit));
		resetTraversalOf();
		return re;
	}
	
	public void setBody(Expression newBody) {
		if (newBody != null) {
			newBody = (Expression) newBody.reduce(METHOD_SET_BODY);
			if (newBody.equals(body)) return;
		}
		
		body = newBody;
		if (body != null) {
			checkCircularDependency();
			setType(body.getType());
			if (!tests(body.isGlobal())) body.setScope(this, this);
		}
	}

	
	
	/**
	 * A function (not reference) negation means body negated.
	 * 
	 * @see ompca.condition.Expression#negate()
	 */
	@Override
	public Expression negate() {
		throwTodoException("boolean function negation");
		return null;
	}

	/**
	 * This is a mutable operation.
	 * 
	 * @see ompca.condition.Expression#reduceOnce()
	 */
	@SuppressWarnings("unchecked")
	@Override
	public Function reduceOnce() {
		setBody(getBody()); 
		super.reduceOnce();
		return this;
	}
	
	
	
	protected void setDirty() {
		super.setDirty();
		// circularIndependentFunctions == null when super classes are being initialized
		if (circularIndependentFunctions != null) circularIndependentFunctions.clear();
	}
	
	protected void checkCircularDependency() {
		checkCircularDependency(this, null);
	}
	
	protected void checkCircularDependency(Function targetCaller) {
		checkCircularDependency(targetCaller, null);
	}

	protected void checkCircularDependency(Function targetCaller, List<Function> callPath) {
		if (circularIndependentFunctions.contains(targetCaller)) return;
		if (isGround()) return;
		if (callPath == null) callPath = Arrays.asList(this);

//		initiatesGettingFrs = true;
		
		Set<Function> calleeRefs = getDirectFunctionReferences();
		if (!equalsFunction(targetCaller) && calleeRefs.contains(targetCaller)) 
			// TODO: replaced by Forall x, x > n /\ caller(x, ...) -> callee(x, ...) 
			throwImcomparableCircularDependencyException(targetCaller, callPath);
		else for (Function callee : calleeRefs) if (callee != this) {
			List<Function> calleePath = new ArrayList<>(callPath);
			calleePath.add(callee);
			callee.checkCircularDependency(targetCaller, calleePath);
		}
		circularIndependentFunctions.add(targetCaller);
		
//		initiatesGettingFrs = false;
	}

	
	
	@Override
	protected Set<ArithmeticGuard> cacheArithmeticGuards() {
		try {
			final Set<ArithmeticGuard> ags = new HashSet<>();
			for (VariablePlaceholder<?> param : getParameters()) 
				Elemental.addAllSkipNull(ags, ()-> param.getArithmeticGuards());
			Elemental.addAllSkipNull(ags, ()-> getBody().getArithmeticGuards());
			return ags;
			
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	
	/**
	 * The function references of a function EXCLUDE the calling function 
	 * itself.
	 * 
	 * @see ompca.condition.ConditionElement#cacheDirectFunctionReferences()
	 */
	@Override
	protected Set<Function> cacheDirectFunctionReferences() {
		Set<Function> refs = new HashSet<>(), subRefs;
//		refs.add(this);
		
		for (VariablePlaceholder<?> p : getParameters()) {
			subRefs = p.getDirectFunctionReferences();
			if (subRefs != null) refs.addAll(subRefs);	// refs != subRefs
		}
		addAllSkipNull(refs, ()-> getBody().getDirectFunctionReferences());
		return refs;
	}
	
	@Override
	protected void cacheDirectSideEffect() {
		for (VariablePlaceholder<?> param : getParameters()) 
			andSideEffect(()-> param.getSideEffect());
		andSideEffect(()-> getBody().getSideEffect());
	}
	
	@Override
	protected <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType) {
		final Set<T> vrs = new HashSet<>();
		addAllSkipNull(vrs, ()-> getBody().cacheDirectVariableReferences(refType));
		return vrs;
	}
	
	@Override
	public Set<Pointer> getPointers() {
		Set<Pointer> ps = new HashSet<>();
		for (VariablePlaceholder<?> param : getParameters()) {
			final PlatformType paramType = param.getType();
//			if (paramType == DataType.Pointer || paramType == DataType.Array)	// excluding Void 
			if (paramType instanceof PointerType)								// including Void 
				ps.add((Pointer) paramType);
		}
		addAllSkipNull(ps, ()-> getBody().getPointers());
		return ps;
	}
	

	
	/**
	 * @param f
	 * @param condGen
	 * @return SMT language-based ID to cross C/C++ machines.
	 */
	public static String getID(IFunction f) {
		if (f == null) throwNullArgumentException("function");
		
		String id = f.getName();
		IParameter[] fParams = f.getParameters();	// Varargs is ignored
		if (fParams != null) 
			for (IParameter fp : fParams) 
				id += ("_" + DataType.from(fp.getType()).getID(null));
				// AST language-based ID
//				id += ("_" + ASTUtil.toID(fp.getType()));
		return id;
	}

	/**
	 * @return function signature combined by both function name and 
	 * 	parameter types as it's guaranteed unique by language conventions.
	 */
	public String getID(SerialFormat format) {
//		if (!isInAST()) return VODCondGen.getID(this);
		
		String id = getName();
		for (VariablePlaceholder<?> param : getParameters()) 
			if (!param.isVarargs()) id += ("_" + param.getType().getID(format));
		return id == null || id.isBlank()
				? throwTodoException("null ID")
				: id;
	}

	private static String getID(String name, Parameter[] params) {
		assert name != null;
		
		if (params != null) 
			for (Parameter p : params) name += ("_" + p.getPeer2());
		return name;
	}
	
	@Override
	public FunctionallableRole getThreadRole() {
		final FunctionallableRole br = get(()-> super.getThreadRole(),
				()-> ThreadRoleMatchable.getThreadRole(getBody())),
				pr = ThreadRoleMatchable.getThreadRole(
						getParameters().toArray(new Expression[] {}));
		return pr == null ? br : (FunctionallableRole) pr.derive(br);
	}

	
	
	public boolean isBool() {
		return getType() == DataType.Bool;
	}
	
	@Override
	public boolean isEmpty() {
		assert !getName().isBlank();
		return !testsNot(()-> getBody().isEmpty());
	}
	
	public boolean containsEmpty() {
		return super.containsEmpty() || tests(()-> getBody().containsEmpty());
	}
	
	/* (non-Javadoc)
	 * @see ompca.condition.Expression#containsArithmetic()
	 */
	@Override
	public boolean containsArithmetic() {
		for (VariablePlaceholder<?> param : getParameters()) 
			if (param.containsArithmetic()) return true;
		try {
			return getThrow(
					()-> getBody().containsArithmetic(), 
					()-> false);
			
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}

	

	/* (non-Javadoc)
	 * @see ompca.condition.Expression#isConstant()
	 */
	@Override
	protected Boolean cacheConstant() {
		return Elemental.testsAnySkipNullException(
				()-> getBody().isConstant(), 
				()-> equalsInPlatformLibrary());
	}
	
	@SuppressWarnings("unchecked")
	protected Function toConstantIf() {
		return this;
	}
	
	/**
	 * All functions are global as what are in Z3.
	 * TODO? Z3 local function
	 * 
	 * @see ompca.condition.ConditionElement#cacheGlobal()
	 */
	@Override
	protected Boolean cacheGlobal() {
		return true;
	}

	public boolean isGround() {
		if (isInAST()) return 
				ASTUtil.isGround(ASTUtil.getWritingFunctionDefinitionOf(getASTName()));
		
		Set<Function> fRefs = getDirectFunctionReferences();
		return fRefs == null 
				|| fRefs.isEmpty()
				|| (fRefs.size() == 1 && equalsFunction(fRefs.iterator().next()));	// self-recursion
	}
	
	/**
	 * A main function object representation is not necessary since all 
	 * assertions from the main function are stored in the top level
	 * {@link PathCondition}.
	 * 
	 * @return always false.
	 */
	public boolean isMain() {
		return isInAST() && getCondGen().isInMainFunction(getASTName());
	}
	
//	public boolean isInAST() {
//		if (isInAST == null) isInAST = !super.isInAST() 
//				? false
//				: ASTUtil.getWritingFunctionDefinitionOf(getASTName()) != null;
//		return isInAST;
//	}
	
	public boolean isInLibrary() {
		final String lib = getLibrary();
		if (lib != null) {
			if (lib.isEmpty()) throwNullArgumentException("library name");
			if (VODCondGen.isLibraryFunction(lib, getID((SerialFormat) null))
					|| VODCondGen.isLibraryFunction(lib, getID(SerialFormat.Z3_SMT))) return true;
			throwTodoException("unregistered library function");
		}
		return false;
	}
	
	
	
//	/**
//	 * Equivalent to {@link Collection<Function>#contains(Object)} for that
//	 * {@link TreeSet<Function>#contains(Object)} depends on 
//	 * {@link #compare(Function, Function)} and making circular dependency
//	 * between themselves.
//	 * 
//	 * @param functions
//	 * @return
//	 */
//	private boolean isContainedBy(Iterable<Function> functions) {
//		if (functions != null) //synchronized (functions) {
//			for (Function f : functions) 
//				if (equals(f)) return true;
////		}
//		return false;
//	}
	
	static public boolean isBefore(Function f1, Function f2) {
		return f1 == null ? f2 != null : f1.compare(f1, f2) < 0;
	}
	
	/**<pre>
	 * The comparison between functions favors (direct) calling relation and 
	 * weights more to (direct-)calls than to grounds 
	 * (direct-calling > other calling > ground in absolute value of credits).
	 * 
	 * @return a relative calling order, 
	 * 	in which positive means calling f2 and negative means being called by f2.
	 * 
	 * 	In more detail:
	 * 	Negative infinity	-	if this is a ground function and f2 is NOT,
	 * 							or f2 is main and this is not;
	 * 	Positive infinity	-	if f2 is a ground function and this is NOT,
	 * 							or this is main and f2 is not;
	 * 	Name_order 			-	if BOTH this and f2 are ground;
	 * 	-level				-	if f2 calls this DIRECTLY;
	 * 	level				-	if this calls f2 DIRECTLY;
	 * 	sum{(f1Callee, f2Callee)} + name order -	for others.
	 * 	TODO? Unreachable function, U - positive infinity;
	 * 
	 * TODO? A calling degree difference of two compared functions, 
	 * which is negatively relative to the calling dependency:
	 * 	For any two distinguished functions, f1 and f2, degree(f1) - degree(f2) = 
	 * 
	 * 		degree(M) - name_order = positive infinity - name_order 
	 * 			if f1 is called by Main function, M;
	 * 
	 * 		0 + name_order if both f1 and f2 are grounded;
	 * 
	 * 		min(degree(f2)) + name_order if f1 non-recursively calls f2;
	 * 
	 * 		min(min(degree(f2)) + name_order, degree(M) - name_order) 
	 * 			if f1 both calls f2 and is called by M;
	 * 
	 * @param f2 - null means the main function
	 * @see java.lang.Comparable#compareTo(java.lang.Object)
	 */
	@Override
	public int compareTo(Function f2) {
		if (f2 == null) return Integer.MAX_VALUE;				// global scope first => f1 > f2, f1 - f2 > 0
		if (f2 == this) return 0;								// non-reference equal
//		if (f2 instanceof BooleanFunction) {
//			BooleanFunction bf2 = (BooleanFunction) f2;
//			if (bf2.isReference()) return compareTo(bf2.getReference());
//		}
		
		boolean f1IsMain = isMain(), f2IsMain = f2.isMain();	// then main scope
		if (f1IsMain && f2IsMain) return 0;
		//* 	infinity Positive 	-	or f2 is main and this is not, f1 > f2, f1 - f2 > 0;
		if (!f1IsMain && f2IsMain) return Integer.MAX_VALUE;
		//* 	Negative infinity	-	or this is main and f2 is not, f1 < f2, f1 - f2 < 0;
		if (f1IsMain && !f2IsMain) return Integer.MIN_VALUE;
		
//		COMPARE_RESULTS.clear();
		Integer res = COMPARE_RESULTS.get(this, f2);
		if (res != null) return res;
		
		int groundDiff = getID((SerialFormat) null).compareTo(f2.getID((SerialFormat) null));
//		if (paramsSup != null) for (Variable p : paramsSup) groundDiff += p.hashCode();
//		if (f2.params != null) for (Variable p2 : f2.params) groundDiff -= p2.hashCode();
//		if (groundDiff > MaxGroundDifference) MaxGroundDifference = groundDiff;

		final int prime = 31, levelDiff = prime * Math.abs(groundDiff);
		Set<Function> f1Refs = getDirectFunctionReferences(), 
				f2Refs = f2.getDirectFunctionReferences();
		try {
			boolean f1IsGround = isGround(), f2IsGround = f2.isGround();
			
			// avoiding mutual inclusion instead of circular traversal
			if (f1Refs.contains(f2) && f2Refs.contains(this))
				throwImcomparableException(this, f2, "mutual inclusion");
			
			//* 	-level				-	if f2 calls this DIRECTLY;
			//* 	Negative infinity	-	if this is a ground function and f2 is NOT, f1 < f2, f1 - f2 < 0
			if (f1IsGround && !f2IsGround) {
				assert f2Refs != null && !f2Refs.isEmpty();
				return cacheCompare(f2, f2Refs.contains(this) ? -levelDiff : Integer.MIN_VALUE);
			}
			//* 	level				-	if this calls f2 DIRECTLY;
			//* 	Positive infinity	-	if f2 is a ground function and this is NOT, f1 > f2, f1 - f2 > 0
			if (!f1IsGround && f2IsGround) {
				assert f1Refs != null && !f1Refs.isEmpty();
				return cacheCompare(f2, f1Refs.contains(f2) ? levelDiff : Integer.MAX_VALUE);
			}
			//* 	Name_order 			-	if BOTH this and f2 are ground;
			if (f1IsGround && f2IsGround) return cacheCompare(f2, groundDiff);
			
		} catch (Exception e) {
			throwTodoException("In-comparable functions", e);
		}
		
		//* 	sum{(f1Callee, f2Callee)} + name order -	for others.
		int subDiff = groundDiff, calleeDiff = subDiff;
		for (Function f1Callee : f1Refs) {
			if (f1Callee == this) continue;
			for (Function f2Callee : f2Refs) try {
				// excluding duplicate self-reference comparison
				if (f2Callee == f2 || f1Callee == f2Callee) continue;
//				if (!f1Callee.startsCircularTraverse() 
//						&& !f2Callee.startsCircularTraverse()) {
//					f1Callee.startCircularTraverse();
//					f2Callee.startCircularTraverse();
//				}
				calleeDiff = compare(f1Callee, f2Callee);
				subDiff = Math.addExact(subDiff, Math.multiplyExact(prime, calleeDiff));
			} catch (NullPointerException e) {
				continue;
			} catch (ArithmeticException e) {
				subDiff = calleeDiff;
			}
		}
		return cacheCompare(f2, subDiff);
	}

	/**
	 * @param f1 - null means the global (main) function
	 * @param f2 - null means the global (main) function
	 * @see java.util.Comparator#compare(java.lang.Object, java.lang.Object)
	 */
	@Override
	public int compare(Function f1, Function f2) {
		return compare2(f1, f2);
	}

	/**
	 * @param f1
	 * @param f2
	 * @return the calling order difference between f1 and f2
	 */
	static public int compare2(Function f1, Function f2) {
		if (f1 == null) return f2 == null ? 0 : Integer.MIN_VALUE;
		return f1.compareTo(f2);
	}
	
	static public Comparison compareIn(Function f1, Function f2) {
		int result = compare2(f1, f2);
		if (result == 0) return Comparison.equals;
		if (result < 0) return Comparison.isBefore;
		return Comparison.isAfter;
	}
	
	private int cacheCompare(Function f2, int result) {
//		stopCircularTraverse();
		COMPARE_RESULTS.put(this, f2, result);
		return result;
	}
	
	/**
	 * @param f1
	 * @param f2
	 * @param msg
	 */
	static protected void throwImcomparableException(Function f1, Function f2, String msg) {
		assert f1 != null && f2 != null && msg != null;
		
		throwTodoException("Imcomparable functions: " + msg + " of " + 
		(f1 == null ? "null" : f1.getID((SerialFormat) null)) + " and " + 
		(f2 == null ? "null" : f2.getID((SerialFormat) null)) + "!");
	}

	/**
	 * @param callerPath
	 * @param msg
	 */
	protected void throwImcomparableCircularDependencyException(
			Function targetCaller, List<Function> callerPath) {
		if (targetCaller == null || callerPath == null) return;
		
		String msg = "Imcomparable functions: circular dependency of ";
		for (Function caller : callerPath) msg += (caller.getID((SerialFormat) null) + " -> ");
		msg += targetCaller.getID((SerialFormat) null);
		throwTodoException(msg);
	}
	
	/**
	 * @return true if this function runtime-logically (dynamically) depends on {@code e}.
	 * @see ompca.condition.Expression#dependsOn(ompca.condition.Expression)
	 */
	public Boolean dependsOn(Expression e) {
		if (e == null) return false;
		
		for (VariablePlaceholder<?> p : getParameters())
			if (p.dependsOn(e)) return true;
		return tests(()-> getBody().dependsOn(e));
	}

	/**
	 * @param f2
	 * @return true if this function statically or dynamically depends on {@code f2}.
	 */
	public boolean dependsOn(Function f2) {
		if (f2 == null) return false;
		
		// AST dependency: in nested locality (static) or runtime calling (dynamic)
		if (isInAST() && f2.isInAST()) return ASTUtil.dependsOn(
				ASTUtil.getWritingFunctionDefinitionOf(getASTName()), 
				ASTUtil.getWritingFunctionDefinitionOf(f2.getASTName()));
		// runtime logical (dynamic) dependency in call cache
		throwTodoException("Dependency in call cache");
//		for (ALL_CALLS);
		return dependsOn((Expression) f2);
	}

	public boolean dependsOn(FunctionCall<?> call) {
		if (call == null) return false;
		
		if (equals(call.getSubject())) return true;
		return dependsOn((Expression) call);
	}

	
	
	/**
	 * Applying signature equivalence checking {@link #equalsFunction(Function)}.
	 * 
	 * ID-based equivalence/hashing depends on disambiguating symbols in the 
	 * {@link HashMap}-based symbol table, which circularly depends on this 
	 * function's hash code, and makes it infeasible.
	 * 
	 * @see ompca.condition.Referenceable#equals(java.lang.Object)
	 */
	protected boolean equalsToCache(SystemElement e2) {
		return equalsFunction((Function) e2);
//			Function f2 = (Function) obj;
//			Expression body2 = f2.body;
//			String id1 = getID(null);
//			if (id1 == null || !id1.equals(f2.getID(null))) return false;
//			assert id1 == f2.getID();
//			return paramsSup.equals(f2.params); 
//					&& ((body == null) ? body2 == null : body.equals(body2)) 
//					&& super.equals(f2);
//		}
	}
	
	/**
	 * Conventional signature equivalence checking.
	 * 
	 * @param f2
	 * @return
	 */
	public boolean equalsFunction(Function f2) {
		if (f2 == null) return false;
		if (f2 == this) return true;
		
		return library != null && library.equals(f2.library)
				&& getID((SerialFormat) null).equals(f2.getID((SerialFormat) null));
//				&& (paramsSup == null ? f2.params == null : paramsSup.equals(f2.params));
	}

	/**
	 * @param callProp
	 * @return
	 */
	public boolean equalsFunction(CallProposition callProp) {
		return callProp == null 
				? false : equalsFunction(callProp.getCallFunction());
	}
	
	/**
	 * @return
	 */
	public Boolean equalsInPlatformLibrary() {
		try {
			return VODCondGen.getPlatformLibraryFunction(
					SerialFormat.Z3_SMT, library, getName()) != null;
		} catch (IllegalStateException e) {
			return null;
		}
	}
	
	/**
	 * Applying signature hashing.
	 * 
	 * ID-based equivalence/hashing depends on disambiguating symbols in the 
	 * {@link HashMap}-based symbol table, which circularly depends on this 
	 * function's hash code, and makes it infeasible.
	 * 
	 * @see #equalsFunction(Function)
	 * @see ompca.condition.Referenceable#hashCode()
	 */
	protected List<Integer> hashCodeVars() {
		final List<Integer> hcvs = new ArrayList<>();
		hcvs.add(library == null ? 0 : library.hashCode());
		hcvs.add(getName().hashCode());
		for (VariablePlaceholder<?> p : getParameters()) 
			hcvs.add(p.getType().hashCode());
		return hcvs; 
	}

	
	
	public boolean hasVarargs() {
		final int psize = getParameterSize();
		return psize > 0 && getParameter(psize - 1).isVarargs();
	}
	
	public boolean suitsSideEffect() {return true;}
	

	
	/**
	 * @param funcs
	 * @return a sorted list instead of a sorted set to ensure all 
	 * 	referencing (logically equal) functions are included.
	 */
	static public List<Function> sort(Set<? extends Function> funcs) {
		if (funcs == null) return null;
		
		List<Function> sfl = new ArrayList<>(funcs);
//		SortedSet<Function> sfs = Collections.synchronizedSortedSet(new TreeSet<>(f));
		if (!funcs.isEmpty()) sfl.sort(funcs.iterator().next());
		return sfl;
	}
	
	
	
	/* (non-Javadoc)
	 * @see ompca.condition.Expression#toProposition()
	 */
	@Override
	public Proposition toProposition() {
		return get(()-> getBody().toProposition(),
				()-> super.toProposition());
	}
	
	/**<pre>
	 * Representing a self-recursive calling where the call scope is its hosting function.
	 * 
	 * See Case II at {@link Proposition#andReduceByFunctions(Proposition)} or
	 * 	{@link Proposition#reduceByFunctions(Operator, Proposition, Proposition)}.
	 * 
	 * </pre>
	 * 
	 * @param op
	 * @param sideEffect
	 * @return
	 */
	public CallProposition toSideEffectCall(Proposition sideEffect) {
		return toSideEffectCall(sideEffect, this);
	}
	
	public CallProposition toSideEffectCall(
			CallProposition sideEffect, ConditionElement callScope) {
		if (sideEffect == null) return null;
		// assert sideEffect.getDirectFunctionReferences() != null;
		// assert !sideEffect.getDirectFunctionReferences().isEmpty();
		if (sideEffect.getDirectFunctionReferences().iterator().next() == this) return sideEffect;
		return toSideEffectCall((Proposition) sideEffect, callScope);
	}
	
	public CallProposition toSideEffectCall(
			Proposition sideEffect, ConditionElement callScope) {
		if (sideEffect == null || !equalsFunction(sideEffect.getFunctionScope())) 
			return null;
		
		// TODO? extracting arguments from caller function of callScope
		final BooleanFunction bf = BooleanFunction.from(this, sideEffect);
		final IName bfAstName = bf.getIName();
		final CallProposition cp = bfAstName != null
				? bf.getCallProposition(bfAstName, null, callScope)
				: bf.getCallProposition(bf.getName(), null, callScope);
		/* adding call proposition side-effect in case of: 
		 * (1) non-recursive calling with non-duplicate proposition 
		 * - !equals(callScope) && !equalsFunction(bf)
		 * or (2) self-recursive calling - equals(callScope) && equalsFunction(bf)
		 */
		final boolean isRc = equals(callScope), isDp = equalsFunction(bf);
		if ((!isRc && !isDp) || (isRc && isDp)) andSideEffect(()-> cp);
		return cp;
		
//		if (body == null || isBool()) setBody(sideEffect);
//		else {
//			oldSe = body instanceof Proposition ? (Proposition) body : getSideEffect();
//			
//			// causing new version of boolean function to be generated
//			op == null -> bodyRelNew = sideEffect;
//			
//			if (op instanceof Proposition.Operator) switch ((Proposition.Operator) op) {
//			case And: 			newSe = oldSe.and(sideEffect); 		break;
//			case Or:			newSe = oldSe.or(sideEffect); 		break;
//			case Xor:			newSe = oldSe.xor(sideEffect); 		break;
//			case Iff:			newSe = oldSe.iff(sideEffect); 		break;
//			case Imply:			newSe = sideEffect.imply(oldSe); 	break;
//			case Not:			newSe = sideEffect == null 
//					? oldSe.not() : sideEffect.not(); 				break;
//			case True:			newSe = Proposition.TRUE; 			break;
//			case False:			newSe = Proposition.FALSE; 			break;
//			case FunctionCall:	newSe = sideEffect; 				break;
//			}
//			
//			// avoiding addSideEffect -> andByReduce -> reduceByFunction -> addSideEffect 
//			if (!initiatesTraversalOf(this)) {
//				initiateTraversalOf(this);
//				addSideEffect(sideEffect);
//				resetTraversalOf(this);
//			}
//		}
	}


	
	/**
	 * @param format
	 * @return
	 */
	public static String toDefinitionString(SerialFormat format) {
		Set<Function> fs = Function.getCOnes();
		fs.addAll(BooleanFunction.getAll());
		
		String str = "";
		for (Function f : Function.sort(fs)) str += (f.toZ3SmtString(false, false, false) + "\n");
		return str;
	}
	
	/**
	 * @return
	 */
	protected String toEmptyString() {
		String func = getName() + "(";
		
		boolean hasParams = false;
		for (VariablePlaceholder<?> param : getParameters()) {
			if (hasParams) func += ", ";
			func += param.toNonEmptyString(true);
			hasParams = true;
		}
		
		return func + ")"; 
	}

	/* (non-Javadoc)
	 * @see ompca.condition.ConditionElement#toNonEmptyString(boolean)
	 */
	protected String toNonEmptyString(boolean usesParenthesesAlready) {
		Expression body = getBody();
		return toEmptyString() 
				+ " {\n\t" 
				+ (body == null ? "" : body.toNonEmptyString(usesParenthesesAlready)) 
				+ "}";
	}


	
	@Override
	public String toZ3SmtString(boolean printsVariableDeclaration, 
			boolean printsFunctionDefinition, boolean isLhs) {
		final String id = getID(SerialFormat.Z3_SMT), 
				lf = VODCondGen.getPlatformLibraryFunction(SerialFormat.Z3_SMT, library, id);
		if (lf != null) return lf;
		
		final PlatformType type = getType();
		if (type == null) throwTodoException(id + " has no type!");
		if (type == DataType.Void) return "";
		
//		CONSTANT_FUNCTIONS.clear();
		Expression body = getBody();
		String func = new String();
		final boolean hasBody = body != null;
		if (hasBody) {
			func += "(define-fun ";
		} else {
			if (isInAST()) throwTodoException(id + " SHOULD have a body!");
			func += "(declare-fun ";
		}
		
		func += (id + " (");
		for (VariablePlaceholder<?> param : getParameters()) func += (hasBody 
				? param.toZ3SmtString(true, true, isLhs) 
				: (param.getType().toZ3SmtString(true, true) + " "));
		
		String typeStr = type.toZ3SmtString(false, true), typeBody = typeStr;
		if (hasBody) {
			typeBody += " " + body.toZ3SmtString(false, true, isLhs);
			final String definingTypeFunc = TYPE_BODY_CACHE.get(typeBody);
			if (definingTypeFunc == null) TYPE_BODY_CACHE.put(typeBody, typeStr + " " + id);
			else if (!definingTypeFunc.endsWith(id)) typeBody = definingTypeFunc;
		}
		
		return func + ") " + typeBody + ")";
	}

}