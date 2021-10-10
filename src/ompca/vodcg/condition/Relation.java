/**
 * 
 */
package ompca.vodcg.condition;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.Elemental;
import ompca.MappableList;
import ompca.MultiPartitionable;
import ompca.Pair;
import ompca.vodcg.ASTAddressable;
import ompca.vodcg.ASTException;
import ompca.vodcg.SystemElement;
import ompca.vodcg.UncertainException;
import ompca.vodcg.UncertainPlaceholderException;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.data.ArithmeticGuard;
import ompca.vodcg.condition.data.Pointer;
import ompca.vodcg.condition.version.FunctionallableRole;
import ompca.vodcg.condition.version.NoSuchVersionException;
import ompca.vodcg.condition.version.ThreadRoleMatchable;
import ompca.vodcg.condition.version.Version;

/**
 * @author Kao, Chen-yi
 *
 */
//TODO? public abstract class Relation<O extends Relation.Operator> 
@SuppressWarnings("deprecation")
public abstract class Relation extends Expression 
implements Cloneable, MultiPartitionable, Comparator<MultiPartitionable.Key> {

	/**
	 * Base class for all relational operators.
	 * While Java enum can't extends (abstract) classes but ONLY implements interfaces.
	 *
	 */
	public interface Operator extends Key {
		default public boolean isAssociativeTo(Operator op) {
			if (Elemental.tests(isUnary())) return false;	// unary property takes the highest priority
			if (Elemental.tests(()-> isConstant() && op.isConstant())) return true;
			return false;
		}
		default public boolean isCommutative() {
			if (Elemental.tests(isUnary())) return false;	// unary property takes the highest priority
			if (Elemental.tests(isConstant())) return true;
			return false;
		}
		default public Boolean isConstant() {return null;}
		default public boolean isMonotonic() {
			return !isCommutative();
		}
		default public Boolean isUnary() 	{return null;}
		default public boolean isBitwise()	{return false;}

		/**
		 * @return
		 */
		default public Operator invert() {return negate();}
		public Operator negate();

		public <H extends Relation> String toZ3SmtString(
				H host, boolean printsVariableDeclaration, boolean printsFunctionDefinition);

	}



//	protected static final UnsupportedOperationException UNSUPPORTED_EXCEPTION = 
//			new UnsupportedOperationException("Unsupported for a final relation!");

	private final static Method METHOD_GET_FILE_LOCATION = 
			Elemental.getMethod(Relation.class, "getFileLocation");
	private final static Method METHOD_GET_POINTERS = 
			Elemental.getMethod(Relation.class, "getPointers");
	private final static Method METHOD_CACHE_DIRECT_SIDE_EFFECT = 
			Elemental.getMethod(Relation.class, "cacheDirectSideEffect");
	private static final Method METHOD_CACHE_FUNCTION_SCOPE = 
			Elemental.getMethod(Relation.class, "cacheFunctionScope");
	private static final Method METHOD_CACHE_SCOPE = 
			Elemental.getMethod(Relation.class, "cacheScope");
	private final static Method METHOD_DEPENDS_ON = 
			Elemental.getMethod(Relation.class, "dependsOn", Expression.class);
	private final static Method METHOD_DEPENDS_ON_2 = 
			Elemental.getMethod(Relation.class, "dependsOn", Relation.class, StringBuffer.class, boolean.class);
	private final static Method METHOD_REDUCE_ONCE = 
			Elemental.getMethod(Relation.class, "reduceOnce", Collection.class);
	private final static Method METHOD_REDUCE_ONCE_2 = 
			Elemental.getMethod(Relation.class, "reduceOnce", List.class);

	/**
	 * Empty operand collection supplier
	 */
	private Supplier<Collection<? extends Expression>> eocSup = null;
	private Collection<? extends Expression> operands = null;
	private Operator op = null;

	/**
	 * Representing constant in CondGen's execution
	 */
	private boolean isFinal;
	
	final private Map<Expression, Pair<Relation, String>> dependency = new MappableList<>();
//	final private DuoKeyMapList<Expression, Relation, String> dependency = new DuoKeyMapList<>();
//	final private List<Expression> independency = new ArrayList<>();
	final private Map<Operator, Set<Relation>> ignoresDependency = new HashMap<>();

	private List<Relation> partKeyOperands = null;


	
	protected Relation(Operator operator, final ASTAddressable rtAddr, VODCondGen condGen, boolean isFinal) {
		super(rtAddr, condGen);
		
		if (operator == null) throwInvalidityException("Must specify the operator!");
		op = operator;
		this.isFinal = isFinal;
	}

	/**
	 * Convenient constructor for the constant (final) elements.
	 * 
	 * @param operator
	 * @param condGen
	 */
	protected Relation(Operator operator, VODCondGen condGen) {
		this(operator, null, condGen, true);
		setConstant(true);
	}
	
	/**
	 * Basic constructor handling relation operands.
	 * 
	 * @param operator
	 * @param operands - maybe empty but NOT null
	 * @param condGen
	 * @param initiatesSideEffect
	 * @param isFinal - flag for constant or memory saving relations.
	 */
	@SuppressWarnings("unchecked")
	protected <O extends Collection<? extends Expression>> Relation(Operator operator, 
			O operands, Supplier<O> operandsConstructor, final ASTAddressable rtAddr, VODCondGen condGen, 
			boolean initiatesSideEffect, boolean isFinal) {
		this(operator, rtAddr, condGen, false);

		eocSup = (Supplier<Collection<? extends Expression>>) operandsConstructor;
		addAll(operands);
		this.isFinal = isFinal;
	}
	
	protected <O extends Collection<? extends Expression>> Relation(Operator operator, 
			O operands, Supplier<O> operandsConstructor, final ASTAddressable rtAddr, VODCondGen condGen, boolean isFinal) {
		this(operator, operands, operandsConstructor, rtAddr, condGen, false, isFinal);
	}

	protected <O extends Collection<? extends Expression>> Relation(Operator operator, 
			O operands, Supplier<O> operandsConstructor, final ASTAddressable rtAddr, VODCondGen condGen) {
		this(operator, operands, operandsConstructor, rtAddr, condGen, false);
	}
	
	/**
	 * @param operator
	 * @param operands - assumed non-empty
	 */
	protected <O extends Collection<? extends Expression>> Relation(Operator operator, 
			O operands, Supplier<O> operandsConstructor) {
//		assert operands != null && !operands.isEmpty();
		this(	operator, 
				operands, 
				operandsConstructor,
				operands.iterator().next().cacheRuntimeAddress(), 
				operands.iterator().next().getCondGen(), 
				false);
	}
	
	protected Relation(Operator operator, 
			Supplier<Collection<? extends Expression>> operandsConstructor, final ASTAddressable rtAddr, VODCondGen condGen) {
		this(	operator, 
				operandsConstructor.get(), 
				operandsConstructor,
				rtAddr,
				condGen, 
				false);
	}
	
	protected Relation(Operator operator, Set<? extends Expression> operands, final ASTAddressable rtAddr, VODCondGen condGen) {
		this(	operator, 
				operands, 
				()-> new HashSet<>(),
				rtAddr,
				condGen, 
				false);
	}
	
	protected Relation(Operator operator, List<? extends Expression> operands, final ASTAddressable rtAddr, 
			VODCondGen condGen, boolean isFinal) {
		this(	operator, 
				operands, 
				()-> new ArrayList<>(),
				rtAddr,
				condGen, 
				false, isFinal);
	}
	
	protected Relation(Operator operator, List<? extends Expression> operands, VODCondGen condGen) {
		this(	operator, 
				operands, 
				operands.isEmpty() ? null : operands.get(0).cacheRuntimeAddress(), 
				condGen, 
				false);
	}
	
	/**
	 * A convenient constructor for unary relations.
	 * 
	 * @param operator
	 * @param operand
	 * @param condGen
	 */
	protected <RelationalExpression extends Expression> Relation(
			Operator operator, RelationalExpression operand) {
		this(operator, 
//				Collections.singletonList(operand), 
//				()-> new ArrayList<>(), 
				Collections.singleton(operand), 
				()-> new HashSet<>(), 
				operand.cacheRuntimeAddress(),
				operand.getCondGen());
		assert operand != null;
	}
	
	/**
	 * A convenient constructor for binary ordered relations.
	 * 
	 * @param operator
	 * @param left_operand
	 * @param right_operand
	 */
	protected <RelationalExpression extends Expression> Relation(Operator operator, 
			RelationalExpression left_operand, RelationalExpression right_operand) {
		this(operator, ()-> new ArrayList<>(), left_operand.cacheRuntimeAddress(), left_operand.getCondGen());
		// TODO: leftOperand.getScope() \/ rightOperand.getScope()
		
		assert left_operand != null;
		if (right_operand == null) throwNullArgumentException("operands. Empty or null are NOT allowed");

		add(left_operand, right_operand);
	}
	
	
	
	@Override
	protected ConditionElement cacheScope() {
		ConditionElement s = null;
		if (!enters(METHOD_CACHE_SCOPE)) {
			enter(METHOD_CACHE_SCOPE);
			for (Expression oprd : getOperands()) 
				s = getCommonScope(s, oprd.getScope());
			leave(METHOD_CACHE_SCOPE);
		}
		return s;
		
//		if (initiatesGettingScope) return null;
//		
//		initiatesGettingScope = true;
//		ConditionElement scope = super.getScope(), commonScope = scope;
//		// lazy scope setting
//		if (scope == null && !isGlobal() && !isEmpty()) {
//			for (Expression oprd : operands) {
//				if (oprd.isConstant()) continue;
//				scope = oprd.getScope();
//				// \/ oprd.scope: scope = scope.or(oprd.getScope());
//				if (scope != null && scope != this) {
//					if (commonScope == null) 
//						commonScope = scope;
//					else if (commonScope != scope) 
//						commonScope = scope.getCommonScope(commonScope);
//				}
//				if (commonScope != null && commonScope.equalsGlobal()) break;
//			}
//			if (commonScope != null) setScope(commonScope);
//		}
//		initiatesGettingScope = false;
//		
//		return commonScope;
	}
	
	@Override
	protected Function cacheFunctionScope() {
		Function fs = null;
		if (!enters(METHOD_CACHE_FUNCTION_SCOPE)) {
			enter(METHOD_CACHE_FUNCTION_SCOPE);
			for (Expression oprd : getOperands()) 
				fs = getCommonFunctionScope(fs, oprd.getFunctionScope());
			leave(METHOD_CACHE_FUNCTION_SCOPE);
		}
		return fs;
	}
	
	@Override
	protected Set<Function> cacheDirectFunctionReferences() {
		Set<Function> refs = new HashSet<>();
		for (Expression oprd : getNonSelfOperands()) 
			refs.addAll(oprd.getDirectFunctionReferences());
		return refs;
	}
	
	/**
	 */
	@Override
	final protected void cacheDirectSideEffect() {
		if (enters(METHOD_CACHE_DIRECT_SIDE_EFFECT)) 
			throwUncertainException(METHOD_CACHE_DIRECT_SIDE_EFFECT);
		
		// containing ONLY operands' side-effect
//		final VODConditions dse = new VODConditions(getCondGen());	
		for (Expression oprd : getOperands()) {
			if (oprd == null) throwNullArgumentException("operand");
			if (oprd == this) continue;	// bypassing special relation
			try {
				if (!guardThrow(()-> cacheOperandDirectSideEffect(oprd), 
						METHOD_CACHE_DIRECT_SIDE_EFFECT)) 
					break;
			
//			} catch (IllegalStateException e) {
//				if (isUncertainException(e)) continue;
//				else {leave(METHOD_CACHE_DIRECT_SIDE_EFFECT); throw e;}
			} catch (Exception e) {
				// at least ClassCastException
				throwTodoException("unsupported operand type", e, METHOD_CACHE_DIRECT_SIDE_EFFECT);
			}
		}
//		andSideEffect(()-> dse);
	}
	
	/**
	 * For caching non-null operand-only side-effects.
	 * 
	 * Default conflict-free co-existing side-effect:
	 * SE = A1.SE && A2.SE && ... && An.SE
	 * 
	 * @param <OT>
	 * @param oprd
	 * @return true if continue to the next operands; 
	 * 	false to break the operands traversal.
	 * @throws ClassCastException
	 */
	protected <OT extends Expression> boolean cacheOperandDirectSideEffect(final OT oprd)
			throws ClassCastException, UncertainException, UncertainPlaceholderException {
		if (oprd == null) throwNullArgumentException("operand");
		
		if (oprd.suitsSideEffect()) andSideEffect(()-> oprd.getSideEffect());
		return true;
	}

	@Override
	public boolean suitsSideEffect() {
		for (Expression oprd : getOperands()) {
			if (oprd == null) throwNullArgumentException("operand");
			if (oprd == this) continue;	// bypassing special relation
			if (oprd.suitsSideEffect()) return true;
		}
		return false;
	}

	
	
	@Override
	public IASTFileLocation getFileLocation() {
		if (!enters(METHOD_GET_FILE_LOCATION)) {
			enter(METHOD_GET_FILE_LOCATION);
			
			for (Expression oprd : getOperands()) {
				if (oprd == null) throwNullArgumentException("operand");
				if (oprd == this) continue;	// bypassing special relation
				
				IASTFileLocation loc = oprd.getFileLocation();
				if (loc != null) return loc;
			}
			
			leave(METHOD_GET_FILE_LOCATION);
		}
		return null;
	}
	
	
	
	@Override
	protected <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType) {
		final Set<T> vrs = new HashSet<>();
		for (Expression oprd : getOperands()) {
			if (oprd == null) throwNullArgumentException("operand");
			if (oprd == this) continue;	// bypassing special relation
			
			@SuppressWarnings("unchecked")
			final Set<T> subVrs = (Set<T>) 
			oprd.getDirectVariableReferences(refType);
			if (subVrs != null) vrs.addAll(subVrs);
//				if (subVrs != null && !subVrs.isEmpty() && !vrs.addAll(subVrs)) 
//					throwTodoException("adding failed", null, METHOD_GET_DIRECT_VARIABLE_REFERENCES);
//			throwTodoException("missing any variable reference?"),
		}
		return vrs;
	}
	

	
	@Override
	protected Set<ArithmeticGuard> cacheArithmeticGuards() {
		// root (side-effect) guards
		final Set<ArithmeticGuard> guards = new HashSet<>();
		// leaf guards
		for (Expression oprd : getOperands()) {
			if (oprd == null) throwNullArgumentException("operand");
			if (oprd == this) continue;	// bypassing special relation
			
			guards.addAll(oprd.getArithmeticGuards());
		}
		return guards;
	}
	
	
	
	public Expression getLeftHandSide() {
		return isBinary()
				? toList().get(0)
				: null;
	}
	
	public Expression getRightHandSide() {
		return isBinary()
				? toList().get(1)
				: null;
	}
	
	@Override
	public IASTStatement getPrivatizingBlock() {
		IASTStatement pb = null;
		try {
			for (Expression oprd : getOperands()) {
				if (oprd == this) continue;	// bypassing special relation

				final IASTStatement opb = oprd.getPrivatizingBlock();
				if (pb == null) pb = opb;
				else if (pb != opb && opb != null) 
					throwTodoException("inconsistent privatizing blocks");
			}
			
		} catch (Exception e) {
			throwTodoException(e);
		}
		return pb;
	}
	
	/**
	 * @return non-null
	 */
	@Override
	public Set<Pointer> getPointers() {
		Set<Pointer> ps = new HashSet<>();
		if (!enters(METHOD_GET_POINTERS)) {
			enter(METHOD_GET_POINTERS);
			
			for (Expression oprd : getOperands()) {
				if (oprd == null) throwNullArgumentException("operand");
				if (oprd == this) continue;	// bypassing special relation
				
				Set<Pointer> subPs = oprd.getPointers();
				if (subPs != null) ps.addAll(subPs);
			}

			leave(METHOD_GET_POINTERS);
		}
		return ps;
	}
	

	
	@Override
	public FunctionallableRole getThreadRole() {
		return get(()-> super.getThreadRole(),
				()-> ThreadRoleMatchable.getThreadRole(getOperands()));
	}

	
	
	@SuppressWarnings("unchecked")
	public <O extends Operator> O getOp() {return (O) op;}
	
	public Expression getOperand(int index) {
		return operands instanceof List
				? toList().get(index)
				: throwTodoException("unsupported operands");
	}
	
	public Expression getOperand1() {
		return getOperands().iterator().next();
	}
	
	public Expression getOperand2() {
		final Iterator<? extends Expression> it = getOperands().iterator();
		it.next();
		return it.next();
	}
	
	/**
	 * Guarded operands getter for a logically empty/non-empty relation.
	 * 
	 * @return a non-null read-only collection of operands for consistent operand data.
	 */
	public Collection<? extends Expression> getOperands() {
		return getRawOperands();
	}
	
	public Collection<? extends Expression> getNonSelfOperands() {
		final Collection<? extends Expression> ros = getRawOperands();
		for (Expression o : ros) if (o == this || o == null) {
			if (ros.remove(o)) break;
			else throwTodoException("unsuccessful remove");
		}
		return ros;
	}
	
	final protected Collection<? extends Expression> getRawOperands() {
		if (eocSup == null) {
			if (operands == null) return Collections.emptyList();
			if (hasOnlyOperand()) return Collections.singletonList(getFirstRawOperand());
			throwNullArgumentException("operand collection supplier");
		}
		
		@SuppressWarnings("unchecked")
		final Collection<Expression> os = (Collection<Expression>) eocSup.get();
		if (operands != null) os.addAll(operands);
		return os;
//		return Collections.synchronizedCollection(Collections.unmodifiableCollection(operands));
	}
	
	/**
	 * Convenient getter for a unary relation to retrieve its only member 
	 * {@link Expression}.
	 * 
	 * @return
	 */
	public Expression getFirstOperand() {
		return getSkipException(()-> getOperands().iterator().next());
	}
	
	final protected Expression getFirstRawOperand() {
		return getSkipException(()-> operands.iterator().next());
	}
	
	public Collection<Relation> getRelationalOperands() {
		@SuppressWarnings("unchecked")
		final Collection<Relation> ros = (Collection<Relation>) eocSup.get();
		for (Expression e : getOperands()) 
			if (e instanceof Relation) ros.add((Relation) e);
		return ros;
	}

//	/**
//	 * {@link #getOperands()}-consistent framework.
//	 * 
//	 * @return
//	 */
//	public boolean hasOnlyOperand() {
//		@SuppressWarnings("unchecked")
//		Iterator<Expression> oprds = (Iterator<Expression>) getOperands().iterator();
//		return oprds.hasNext() && oprds.next() != null && !oprds.hasNext();
//	}
	public boolean hasOnlyOperand() {
		return operands != null && operands.size() == 1;
	}
	
	/**
	 * Convenient setter for a unary relation to set its only member 
	 * {@link Expression}.
	 * 
	 * CAUTION: ALL OPERANDS WILL BE REMOVED BEFORE SET!
	 * 
	 * @param operand
	 */
	@SuppressWarnings("unchecked")
	public void setOnlyOperand(Expression operand) {
		if (isFinal) throwTodoException("truly final?");

		if (operand == null) operands = null;
		else if (operands != null && operands.size() == 1 && operands.iterator().next() == operand) 
			return;
		else {
			if (operand instanceof Relation) ((Relation) operand).checkDependency(this);
			
			try {
				operands.clear();
				((Collection<Expression>) operands).add(operand);
				
			} catch (NullPointerException | UnsupportedOperationException exc) {
				// for singleton case, where a singleton list actually is also unmodifiable
//			if (operands instanceof List<?>) ((List<Expression>) operands).set(0, operand);
//				operands = Collections.singletonList(operand);
				operands = Collections.singleton(operand);
				eocSup = ()-> new HashSet<>();
			}
		}
		setDirty();
	}

	public int size() {
		return getOperands().size();
	}
	
	
	
	@SuppressWarnings("unchecked")
	public boolean add(Expression e) {
		if (isFinal) throwTodoException("truly final?");
		if (operands == null) {
			if (eocSup == null) throwNullArgumentException("operand collection supplier");
			operands = Collections.synchronizedCollection(eocSup.get());
		}
//		if (!tests(e.isGlobal())) e.fillScope(this);
		setDirty();
		return add((Collection<Expression>) operands, e);
	}
	
	/**
	 * TODO? For binary relations to avoid the single operand exception.
	 * 
	 * @param e1
	 * @param e2
	 * @return
	 */
	public boolean add(Expression e1, Expression e2) {
		return add(e1) && add(e2);
	}
	
	protected boolean add(Collection<Expression> oprds, Expression e) {
		if (oprds == null) throwNullArgumentException("operands");
		if (e == null) throwNullArgumentException("operand");
		if (e instanceof Relation) ((Relation) e).checkDependency(this);
		
		try {
			if (oprds.add(e)) {
				// maybe inconsistent roles b/w operands and oprds
//				if (tests(isAssigned())) setAssigned(e);
			} else 
//				getCondGen().log(null, "duplicate " + e);
				if (!toCanonicalString().contains(e.toCanonicalString())) 
					throwTodoException("wrong addition");
		} catch (UnsupportedOperationException ex) {	// for debugging use
			throwTodoException(ex);
		}
		
		return true;
	}
	
	/**
	 * A newly created relation adds (function) scopes bottom-up;
	 * a muted one merges (function) scopes from both directions.
	 * 
	 * Therefore both scopes and side-effects are lazily computed on demand.
	 * 
	 * @param newOperands
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public boolean addAll(Collection<? extends Expression> newOperands) {
		if (isFinal) throwTodoException("truly final?");
		if (newOperands == null) throwNullArgumentException("operands");
		
		for (Expression ne : newOperands) {
			if (ne == null) throwNullArgumentException("operand");
			if (ne instanceof Relation) ((Relation) ne).checkDependency(this);
//			if (!tests(ne.isGlobal())) ne.fillScope(this);
		}
		
		if (operands == null) 
			operands = Collections.synchronizedCollection(newOperands);
		else try {
			if (!((Collection<Expression>) operands).addAll(newOperands)) {
				final String str = toCanonicalString();
				for (Expression newO : newOperands) 
					if (!str.contains(newO.toCanonicalString())) 
						log("inconsistent canonical string");
			}
		} catch (UnsupportedOperationException ex) {	// for debugging use
			throwTodoException(ex);
		}
		
		setDirty();
		return true;
	}
	
	public boolean remove(Expression e) {
		if (e == null) throwNullArgumentException("operand");
		if (isFinal) throwTodoException("truly final?");
		if (operands == null) return false;
		
		try {
			if (!operands.remove(e) && !toString().contains(e.toString())) 
				throwTodoException("wrong equality");
		} catch (UnsupportedOperationException exc) {
			throwInvalidityException(exc.toString());
		}

		setDirty();
		return true;
	}
	
	/**
	 * @param e
	 * @return maybe a reduced relation (operand expression)
	 */
	public Expression rest(Expression e) {
		if (e == null) throwNullArgumentException("operand");
		
		final Relation r = (Relation) clone();
//		final boolean isF = r.isFinal;
		r.isFinal = false;
		if (r.operands.remove(e)) {
//			r.isFinal = isF;
			return r.reduceOnce();
		}
		return this;
	}
	
	
	
	public Operator nextPartitionKey() {
		Operator op = getOp();
		if (!(op instanceof Enum<?>)) return null;
		
		if (partKeyOperands == null) partKeyOperands = new ArrayList<>();
		if (partKeyOperands.isEmpty()) {
			partKeyOperands.add(this);
			return op;
		}
		else {	// next-layer breadth-first key collecting
			Collection<Relation> oldPkos = 
					Collections.unmodifiableCollection(partKeyOperands);
			List<Operator> partKeyOps = new ArrayList<>();
			partKeyOperands.clear();
			for (Relation opko : oldPkos) 				
				for (Relation r : opko.getRelationalOperands()) {
					partKeyOperands.add(r);
					partKeyOps.add(r.getOp());
				}
			if (partKeyOps.isEmpty()) return null;
			
			//conflict comparator if Enum<?> implements Key, Comparator<Enum<?>>
			Collections.sort(partKeyOps, this);
			return partKeyOps.get(partKeyOps.size()/2);
		}
	}
	
	public int compare(Key op1, Key op2) {
		if (op1 == null) throwNullArgumentException("op1");
		if (op2 == null) throwNullArgumentException("op2");
		
		Class<?> c1 = op1.getClass();
		Class<?> c2 = op2.getClass();
		if (c1 != c2) return Integer.compare(c1.hashCode(), c2.hashCode());
		
		if (!(op1 instanceof Enum<?>)) throwInvalidityException("op1");
		if (!(op2 instanceof Enum<?>)) throwInvalidityException("op2");
		return Integer.compare(((Enum<?>) op1).ordinal(), ((Enum<?>) op2).ordinal());
	}

	
	
	@SuppressWarnings("unchecked")
	private Object clone(java.util.function.Function<Expression, Expression> oprdClone) {
		assert oprdClone != null;

		// Calling {@link Object#clone()} default procedure first
		Relation clone = (Relation) super.cloneNonConstant();
		
		clone.op = op;
		clone.eocSup = eocSup;
		clone.isFinal = isFinal;
		
		/* Then cloning operands (deep-operand copying) case-by-case 
		 * since neither {@link Collection} implements {@link Cloneable} 
		 * nor deep copy clone(), nor {@link Collections} has 
		 * {@link Collections#copy(Collection, Collection)}.
		 */
		cloneOperands: if (operands != null) {	
			if (eocSup == null) {
				if (operands.size() == 1) {
					clone.operands = Collections.singleton(operands.iterator().next());
					break cloneOperands;
				}
				else throwTodoException("unsupported operands type!");
			}
			
			clone.operands = eocSup.get();
			for (Expression oprd : operands)  
				((Collection<Expression>) clone.operands).add(oprdClone.apply(oprd)); 
		}
		return clone;
	}
	
	@Override
	protected Object cloneNonConstant() {
		return clone(oprd -> (Expression) oprd.clone());
	}
	
	/**
	 * @param <T>
	 * @param blockStat
	 * @param role
	 * @param ver
	 * @return a thread-private version explicitly expressing element.
	 * @throws NoSuchVersionException
	 */
	@SuppressWarnings("unchecked")
	@Override
	public <T extends ConditionElement> T cloneReversion(
			IASTStatement blockStat, final FunctionallableRole role, final Version<? extends PathVariable> ver) {
		try {
			final T newCe = (T) super.cloneReversion(blockStat, role, ver);
			if (newCe == this) return (T) this;
			
		} catch (NoSuchVersionException e) {
		}
		return (T) clone(oprd -> oprd.cloneReversion(blockStat, role, ver));
	}

	
	
	/* (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	protected boolean equalsToCache(SystemElement e2) 
			throws ClassCastException, NullPointerException {
		Relation r2 = (Relation) e2;
		if (op != r2.op) 					return false;
		if (!op.equals(r2.op)) 				return false;
		return getOperands().equals(r2.getOperands());
	}
	
	/**
	 * Complying string equivalence.
	 * 
	 * @see ompca.condition.Expression#hashCodeVars()
	 */
	@Override
	protected List<Integer> hashCodeVars() {
		assert op != null;
		return Arrays.asList(op.hashCode(), getOperands().hashCode());
//				+ (operands == null ? hashCodeObject() : operands.toString().hashCode());
	}
	
	
	
	/**
	 * <em>NOTE:</em> May be called during super-class initialization.
	 * @return true for a unit constant or relations without arguments (operands)
	 */
	protected Boolean cacheConstant() {
		if (isEmpty() || isUnitConstant()) return true;
		if (tests(()-> getOp().isConstant())) return true;
		
		for (Expression oprd : getOperands()) {
			if (oprd == null || oprd == this) continue;	// maybe a global constant
//			if (oprd == this) throwInvalidityException("circular dependency");
			
			Boolean isOprdConstant = oprd.isConstant();
			if (isOprdConstant == null) return null;
			if (!isOprdConstant) return false;
		}
		return true;
	}
	
	public boolean isUnitConstant() {
		return operands != null && 
				operands.size() == 1 && 
				operands.iterator().next() == this;
	}
	
	/**
	 * Note this is a mutable overriding.
	 * 
	 * @see ompca.vodcg.SystemElement#toConstant()
	 */
	@SuppressWarnings("unchecked")
	@Override
	protected Expression toConstantIf() 
		throws ASTException, UncertainException {
		operands = toConstantOperands();
		setDirty();
		return this;
	}
	
	/**
	 * @return non-null constant-ized operands
	 */
	protected Collection<Expression> toConstantOperands() 
		throws ASTException, UncertainException {
		if (eocSup == null) {
			if (isUnary()) return Collections.singletonList(getFirstOperand().toConstant());
			throwTodoException("unsupported operand collection");
		}
		
		@SuppressWarnings("unchecked")
		Collection<Expression> newOperands = (Collection<Expression>) eocSup.get();
		for (Expression oprd : getOperands())
			newOperands.add((Expression) oprd.toConstant());
		return newOperands;
	}
	
	

	@Override
	protected Boolean cacheGlobal() {
		for (Expression oprd : getOperands()) {
			assert oprd != null;
			Boolean isG = oprd.isGlobal();
			if (isG == null) return null;
			if (!isG) return false;
		}
		
//		if (super.cacheGlobal() == Boolean.FALSE) return false;
		
		setGlobal();
		return true;
	}

	public boolean isFinal() {
		return isFinal;
	}
	
	public boolean isUnary() {
		return Elemental.tests(getOp().isUnary()) || getOperands().size() == 1;
	}
	
	public boolean isBinary() {
		return size() == 2;
	}
	
	/**
	 * Operands may be temporarily empty.
	 * 
	 * @see ompca.condition.ConditionElement#isEmpty()
	 * @see ompca.condition.Expression#isSemanticallyEmpty()
	 */
	@Override
	public boolean isEmpty() {
		assert op != null;
		if (operands == null || operands.isEmpty()) return true;
		
		// for empty reference operands without subjects resolved
		for (Expression oprd : operands) 	// getOperands() depends on isEmpty()
			if (oprd != null && oprd != this && !oprd.isEmpty()) return false;
		return true; 
	}
	
	/**
	 * @return true if <em>any</em> operand contains empty.
	 * @see ompca.condition.Expression#containsEmpty()
	 */
	@Override
	public boolean containsEmpty() {
		if (super.containsEmpty()) return true;
//		if (isEmpty()) return true;
		
		for (Expression oprd : getOperands()) 
			if (oprd != this && oprd.containsEmpty()) return true;
		return false; 
	}
	
	
	
	@Override
	public boolean containsArithmetic() {
		for (Expression oprd : getOperands()) 
			if (oprd != this && oprd.containsArithmetic()) return true;
		return false; 
	}
	
	public Boolean containsNonConstArithmetic() {
		for (Expression oprd : getOperands()) 
			if (oprd != this && oprd.containsNonConstArithmetic()) return true;
		return false; 
	}

	
	
	@Override
	public boolean contains(Expression e) {
		if (e == null || isEmpty()) return false;
		return getOperands().contains(e);
	}
	
//	public boolean dependsOnDirectly(Expression exp) {
//	if (super.dependsOnDirectly(exp)) return true;
//	for (Expression e : getOperands())
//		if (e == exp) return true;
//	return false;
//}

	@SuppressWarnings("unlikely-arg-type")
	public boolean containsOperands(Relation r2) {
		if (r2 == null || isEmpty()) return false;
		return getOperands().contains(r2.getOperands());
	}
	
	protected void checkDependency(Relation rel2) {
		checkDependency(null, rel2);
	}
	
	/**
	 * @param op - can be null
	 * @param rel2
	 */
	protected void checkDependency(Operator op, Relation rel2) {
		if (rel2 == null) throwNullArgumentException("relation");
		if (op != null && ignoresDependency(op, rel2)) { 
//			ignoresDependency = false;	// reset for the next optimization
			return;
		}
		
		StringBuffer rosb = new StringBuffer();
		Relation ro = dependsOn(rel2, rosb, false);
		if (ro != null) {
			String opStr = op == null ? "has" : op.toString();
			throwCircularDependencyException(rel2, ro, equals(ro) 
				? rosb.insert(0, "A " + opStr + " ") 
				: rosb.append(" " + opStr + " A"));
		}
	}
	
	public boolean ignoresDependency(Operator op, Relation rel2) {
		if (op == null) throwNullArgumentException("operator");
		if (rel2 == null) throwNullArgumentException("relation");

		return Elemental.get(
				()-> ignoresDependency.get(op).contains(rel2), e-> false);
	}
	
	final public void ignoreDependency(Operator op, Relation rel2) {
		if (op == null) throwNullArgumentException("operator");
		if (rel2 == null) throwNullArgumentException("relation");
		
		try {
			if (!Elemental.addSkipNull(ignoresDependency.get(op), ()-> rel2))
				ignoresDependency.put(op, new HashSet<>(Arrays.asList(rel2)));
			if (op.isCommutative()) 
				if (!Elemental.addSkipNull(rel2.ignoresDependency.get(op), ()-> this))
					rel2.ignoresDependency.put(op, new HashSet<>(Arrays.asList(this)));
		} catch (Exception e) {
			throwUnhandledException(e);
		}
	}
	
	final public void resetIgnoreDependency() {
		ignoresDependency.clear();
	}
	
//	private boolean independsOnCache(Expression e) {
//		for (Expression i : independency) if (i == e) return true;
//		return false;
//	}
	
	@Override
	public Boolean dependsOn(Expression e) {
//		if (independsOnCache(e)) return false;
		if (dependency.containsKey(e)) return true;
		if (enters(METHOD_DEPENDS_ON)) throwReenterException(METHOD_DEPENDS_ON);

		enter(METHOD_DEPENDS_ON);
		final boolean doRel = e instanceof Relation;
		Boolean subdo = null;
		for (Expression operand : getOperands()) {
			if (subdo = operand == e) break;
			
			subdo = operand.dependsOn(e);
			if (subdo == null) if (doRel) 
				for (Expression ee : ((Relation) e).getOperands()) {
					subdo = operand.dependsOn(ee);
					if (subdo == null) continue;
					if (subdo) break;
				}
			if (subdo) break;
		}
		
		if (tests(subdo)) dependency.put(e, new Pair<>());
		return leave(subdo, METHOD_DEPENDS_ON);
//		return !independency.add(e);
	}
	
	/**
	 * @param rel2
	 * @return null if not depend on {@code rel2} in any situation.
	 */
	public Relation dependsOn(Relation rel2) {
		return dependsOn(rel2, null);
	}
	
	/**
	 * @param rel2
	 * @return null if not depend on {@code rel2} in any situation.
	 */
	public Relation dependsOn(Relation rel2, final StringBuffer dependsOnString) {
		return dependsOn(rel2, dependsOnString, false);
	}
	
	/**
	 * @param rel2
	 * @param dependOnString
	 * @param ignoresPredicate - true to indicate that neither this relation 
	 * 	nor {@code rel2} is a {@link Predicate}.
	 * @return null if not depend on {@code rel2} according to 
	 * 	{@code dependsPropositionally}.
	 */
	private Relation dependsOn(Relation rel2, 
			final StringBuffer dependOnString, boolean ignoresPredicate) {
		if (rel2 == null || enters(METHOD_DEPENDS_ON_2)
				|| (ignoresPredicate && (this instanceof Predicate || rel2 instanceof Predicate))
				|| isEmpty() || rel2.isEmpty()) {
//			if (dependsOnString != null) dependsOnString.setLength(0);
			return null;
		}

		// checking cache
//		if (independsOnCache(rel2)) return null;
		Pair<Relation, String> drs = dependency.get(rel2);
		Relation on = null; String dos = null;
		if (drs != null) {
			on = drs.getPeer1(); dos = drs.getPeer2();
			if (on != null) {
				if (dependOnString != null && dos != null) 
					dependOnString.replace(0, dependOnString.length(), dos);
				return on;
			}
		}
		if (this == rel2) {		// logical equals(rel2) doesn't make dependencies
			if (dependOnString != null) {
				dependOnString.setLength(0);
				dependOnString.append("A");
				dos = dependOnString.toString();
			}
			dependOn(rel2, this, dos);
			return this;
		}
		
		boolean is1stRel = true, isUnary = isUnary();
		for (Expression e : getOperands()) 
			if (e instanceof Relation) {
				enter(METHOD_DEPENDS_ON_2);
				on = ((Relation) e).dependsOn(rel2, dependOnString, ignoresPredicate); 
				leave(METHOD_DEPENDS_ON_2);

				if (on != null) {
					dos = null;
					if (dependOnString != null) {
						String opStr = op.toString();
						dependOnString.insert(0, isUnary 
								? opStr + "("
								: "(" + (is1stRel?"":("_ " + opStr + " ")));	// if binary or n-ary
						dependOnString.append(isUnary 
								? ")"
								: (is1stRel?(" " + opStr + " _"):"") + ")");	// if binary or n-ary
						dos = dependOnString.toString();
					}
					dependOn(rel2, on, dos);
					return on;
				}
				is1stRel = false;
			}
		
		if (dependOnString != null) dependOnString.setLength(0);
//		independency.add(rel2);
		return null;
	}
	
	/**
	 * @param rel2
	 * @param on
	 * @param dos
	 */
	private void dependOn(Relation rel2, Relation on, String dos) {
		dependency.put(rel2, new Pair<>(on, dos));
	}

	
	
	/**
	 * @param o1s
	 * @param o2s
	 * @return conjunctive operand derivation.
	 */
	public static boolean derives(Collection<? extends Expression> o1s, Collection<? extends Expression> o2s) {
		if (o1s == null || o2s == null) throwNullArgumentException("operand");
		for (Expression o1 : o1s)
			for (Expression o2 : o2s) if (!o1.derives(o2)) return false;
		return true;
	}
	
	/**
	 * @param exp
	 * @return If this relation has {@code exp} as one of its 'direct' operands 
	 * or not.
	 */
	public boolean relates(Expression exp) {
		return operands != null && operands.contains(exp);
	}
	
	/**
	 * Relates-on relation is mutual dependency.
	 * 
	 * @param rel2
	 * @param relatesOnString
	 * @param relatesPropositionally - true to indicate that neither this relation 
	 * 	nor {@code rel2} is a {@link Predicate}.
	 * @return some common relations or sub-relation of both this relation and 
	 * 	{@code rel2}.
	 */
	private Relation relatesOn(Relation rel2, 
			final StringBuffer relatesOnString, boolean relatesPropositionally) {
		if (rel2 == null) return null;
		
		Relation on = dependsOn(rel2, relatesOnString, relatesPropositionally);
		if (on != null) return on;
		on = rel2.dependsOn(this, relatesOnString, relatesPropositionally);
		if (on != null) return on;
		
		return null;
//		for (Expression e : operands) 
//			if (rel2.relates(e)) return true;
	}
	
	/**
	 * @param rel2
	 * @return some common relation or sub-relation if both this relation and 
	 * 	{@code rel2} are non-{@link Predicate}'s.
	 */
	public Relation relatesOn(Relation rel2, final StringBuffer relatesOnString) {
		return relatesOn(rel2, relatesOnString, false);
	}
	
	/**
	 * @param rel2
	 * @return some common relation or sub-relation if both this relation and 
	 * 	{@code rel2} are non-{@link Predicate}'s.
	 */
	public Relation relatesPropositionallyOn(
			Relation rel2, final StringBuffer relatesOnString) {
		return relatesOn(rel2, relatesOnString, true);
	}

	
	
//	/**
//	 * @param strBuf
//	 */
//	public void setRelatesOnString(StringBuffer strBuf) {
//	}
	
	
	
	@SuppressWarnings("unchecked")
	protected Expression reduceOnce() {
		if (operands != null) {
//			checkDependency(this);	// done at get(...) time
			try {
				if (operands instanceof List<?>) reduceOnce((List<Expression>) operands);
				else reduceOnce((Collection<Expression>) operands);
			} catch (UnsupportedOperationException ex) {
				throwTodoException(ex.toString());
			}
		}
		super.reduceOnce();
		return this;
	}
	
	private void reduceOnce(Collection<Expression> operands) {
		Iterator<?> it = operands.iterator();
		while (it.hasNext()) {
			SystemElement e = (SystemElement) it.next();
			if (e == this) continue;
			
			SystemElement r = e.reduce(METHOD_REDUCE_ONCE);
			if (r != e) {
				it.remove(); 
				((Collection<Expression>) operands).add((Expression) r); 
				break;
			}
		}
	}
	
	private void reduceOnce(List<Expression> operands) {
		ListIterator<Expression> it = operands.listIterator();
		while (it.hasNext()) {
			SystemElement e = (SystemElement) it.next();
			if (e == this) continue;
			
			SystemElement r = e.reduce(METHOD_REDUCE_ONCE_2);
			if (r != e) {
				it.set((Expression) r); 
				break;
			}
		}
	}
	
	
	
	@Override
	protected void setDirty() {
		partKeyOperands = null;

		// for post-initialization-time reset
		if (dependency != null) dependency.clear();
//		if (independency != null) independency.clear();
		
		resetIgnoreDependency();
		super.setDirty();
	}

	public void setFinal() {
		isFinal = true;
	}
	
	
	
	@Override
	@SuppressWarnings("unchecked")
	public <T extends ConditionElement> T substitute(Reference<?> ref1, Reference<?> ref2) {
		// shallow relation substitution
		final T ss = super.substitute(ref1, ref2);
		if (ss != this) return ss;
		
		// deep relation substitution
		if (operands != null && eocSup != null) {
			boolean isS = false;
			final Collection<Expression> newOprds = 
					(Collection<Expression>) eocSup.get();
			for (Expression oprd : operands) {
				final Expression newOprd = debugCallDepth(()-> oprd.substitute(ref1, ref2));
				if (!add(newOprds, newOprd))
					throwTodoException("unsupported addition");
				if (newOprd != oprd) {
					isS = true;
				}
			}
			if (isS) operands = newOprds;
		
		} else 
			throwTodoException("unsupported substitution");

		return (T) this;
	}

	
	
	public Expression[] toArray() {
		return getOperands().toArray(new Expression[]{});
//		return isEmpty() ? null : getOperands().toArray(new Expression[]{});
	}
	
	public Iterator<? extends Expression> toIterator() {
		return getOperands().iterator();
//		return isEmpty() ? null : getOperands().iterator();
	}
	
	public List<? extends Expression> toList() {
		return new ArrayList<>(getOperands());
	}
	
	@SuppressWarnings("unchecked")
	public <T> List<T> toList(Class<T> clazz) {
		final List<? extends Expression> l = toList();
		if (clazz != null) {
			final Iterator<? extends Expression> li = l.iterator();
			while (li.hasNext())
				if (!clazz.isInstance(li.next()))
					li.remove();
		}
		return (List<T>) l;
	}
	
	public Set<? extends Expression> toSet() {
		return new HashSet<>(getOperands());
	}
	
	
	
	protected String toEmptyString() {
		return getOp().toString();
	}
	
	/**
	 * An infix serialization.
	 *  
	 * @see ompca.condition.ConditionElement#toNonEmptyString(boolean)
	 */
	@Override
	protected String toNonEmptyString(boolean usesParenAlready) {
		final Operator op = getOp();
		final String opStr = op == null ? "?" : op.toString();
		final Expression[] operandArray = toArray();
		String str = isUnary() ? opStr : "";
		
		if (operandArray != null) 
		for (int i = 0, iEnd = operandArray.length - 1; i <= iEnd; i++) {
			boolean usesParen = false;
			Expression operandNow = operandArray[i];
//			if (!usesParenAlready && !cond.startsWith("(") 
//					&& operandNow instanceof Relation && !((Relation)operandNow).op.isAssociativeTo(op)) {
//				cond = "(\n\t" + cond;
//				usesParen = true;
//			}
			if (operandNow instanceof Relation) {
				Relation operandRel = (Relation) operandNow;
				operandRel.checkDependency(this);
				usesParen = !operandRel.isUnary() && 
						(((i == 1 || i == iEnd) && !usesParenAlready)
								|| operandRel.op.isAssociativeTo(op));
			}
			if (i >= 1) str += ((usesParen ? "\n" : "") + " " + opStr + " "); 
			if (usesParen) str += "("; 
			str += operandNow.toNonEmptyString(usesParen);
			if (usesParen) str += ")"; 
		}
//		if (usesParen) cond += ")"; 
		
		return str;
	}
	
	/**
	 * @param op - the string form of operator
	 * @param operands
	 * @return
	 */
	public static String toZ3SmtString(String op, Collection<? extends Expression> operands) {
		if (op == null) throwNullArgumentException("operator");
		if (operands == null || !operands.iterator().hasNext()) {
//			Debug.throwInvalidityException("no operands");
			return op;
		}
		
		String str = "(" + op;
		for (Expression oprd : 
			Collections.synchronizedCollection(Collections.unmodifiableCollection(operands))) {
//			if (oprd instanceof Relation) {
//				Relation rel = (Relation) oprd;
//				rel.checkDependency(rel.op, rel);
//			}
//			str += ("\n\t" + oprd.toZ3SmtString(false, false, false));
			str += (" " + oprd.toZ3SmtString(false, false, false));
		}
		
		// for combined ops, such as "not (="
		int idx = -1;
		do {
			str += ")";
			idx = op.indexOf("(", idx + 1);
		} while (idx != -1);
		
		return str;
	}
	
	@Override
	public String toZ3SmtString(
			boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs) {
//		return debugGet(()-> toZ3SmtString(
		return toZ3SmtString(
				getOp().toZ3SmtString(this, printsFunctionDefinition, printsFunctionDefinition), 
				getOperands());
	}

}