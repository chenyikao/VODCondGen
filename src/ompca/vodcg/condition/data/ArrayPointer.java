/**
 * 
 */
package ompca.vodcg.condition.data;


import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.eclipse.cdt.core.dom.ast.IASTArrayDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTArrayModifier;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.Addressable;
import ompca.condition.SerialFormat;
import ompca.vodcg.ASTAddressable;
import ompca.vodcg.ASTException;
import ompca.vodcg.Assignable;
import ompca.vodcg.IncomparableException;
import ompca.vodcg.SystemElement;
import ompca.vodcg.UncertainException;
import ompca.vodcg.UncertainPlaceholderException;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.ConditionElement;
import ompca.vodcg.condition.Expression;
import ompca.vodcg.condition.Function;
import ompca.vodcg.condition.FunctionalPathVariable;
import ompca.vodcg.condition.PathVariable;
import ompca.vodcg.condition.PathVariablePlaceholder;
import ompca.vodcg.condition.Reference;
import ompca.vodcg.condition.VariablePlaceholder;
import ompca.vodcg.condition.version.ArrayAccessVersion;
import ompca.vodcg.condition.version.FunctionallableRole;
import ompca.vodcg.condition.version.NoSuchVersionException;
import ompca.vodcg.condition.version.ThreadRoleMatchable;
import ompca.vodcg.condition.version.Version;

/**
 * For directly mapping an AST array instance.
 * array_pointer = super_array[index] = *(super_array + index)
 * 
 * An array pointer always points to (gets the value of) its containing element/sub-array.
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class ArrayPointer extends Pointer {

//	private static final Map<Stack<IASTArraySubscriptExpression>, Array> ALL_ARRAYS = 
//			new HashMap<>();

	/**
	 * Direct AST-array mapping.
	 * Not using array-variable-version mapping since version may be revised while l-value is constant.
	 */
	private final static Map<Assignable<?>, ArrayPointer> BEGIN_CACHE = new HashMap<>();
	private final static Map<IASTArraySubscriptExpression, Pointer> CACHE = new HashMap<>();
	
	private static boolean isParsingArrayArgument;
	private static Stack<IASTArraySubscriptExpression> arrayASTsInParsing = 
			new Stack<>();

	
	
	/**
	 * If it represents an end delegate, it's stored in the base array.
	 */
	private ArithmeticExpression index = null;
	
	
	
	/**
	 * Constructing an array referring {@code topArray}. 
	 * 
	 * @param i	- maybe null for the array type
	 * @param beginArray - a path variable placeholder containing the end access version
	 * @throws NoSuchVersionException 
	 */
	private ArrayPointer(
			final PathVariablePlaceholder beginArray, final ArithmeticExpression i) {
		super(Operator.Point, beginArray, beginArray.getScopeManager());
		assert beginArray != null;
		
		setIndex(i);
//		setAssigned(topArray.isAssigned());
	}
	
	/**
	 * Constructing an array referring {@code superArray} at {@code i}, s.t.
	 * 
	 * this = superArray[i] = *(superArray + i)
	 * 
	 * @param superArray
	 * @param i
	 */
	private ArrayPointer(final ArrayPointer superArray, final ArithmeticExpression i) 
			throws NoSuchVersionException {
		super(Operator.Point, superArray, superArray.getScopeManager());
		
		assert superArray != null;
		if (superArray.getIndex() == i && !tests(i.isConstant())) 
			throwTodoException("misplaced duplicate index");
		
//		run(()-> ((ArrayAccessVersion) getEndDelegate().getVersion()).addArgument(i));
		setIndex(i);
//		setAssigned(superArray.isAssigned());
	}
	
	private static ArrayPointer from(
			final PathVariablePlaceholder pvp, final IASTArrayDeclarator ad) {
		assert pvp != null && ad != null;
		final List<IASTArrayModifier> ams = Arrays.asList(ad.getArrayModifiers());
		return ams == null || ams.isEmpty()
				? throwTodoException("unsupported array")
				: from(pvp, ams);
	}
		
	private static ArrayPointer from(
			final PathVariablePlaceholder pvp, final List<IASTArrayModifier> ams) {
		assert pvp != null && ams != null && !ams.isEmpty();
		final int argIdx = ams.size() - 1;
		final IASTExpression arge = ams.get(argIdx).getConstantExpression();
		final ArithmeticExpression arg = arge == null 
				? null 
				: (ArithmeticExpression) Expression.fromRecursively(arge, null, pvp.getCondGen());
		return argIdx == 0
				? from(pvp, arg)
				: from(from(pvp, ams.subList(0, argIdx)), arg);

	}
	
	private static ArrayPointer from(
			final PathVariablePlaceholder pvp, final ArithmeticExpression i) {
		assert pvp != null;
		
		final Assignable<?> asn = pvp.getAssignable();
		ArrayPointer top = BEGIN_CACHE.get(asn);
		if (top == null) 
			BEGIN_CACHE.put(asn, top = new ArrayPointer(pvp, i));
//		try {
//			// reversion array with argument i
//			pvp.reversion(top.getArguments());
//		} catch (NoSuchVersionException e) {
//			throwTodoException(e);
//		}
		return top;
	}
	
	private static ArrayPointer from(
			final ArrayPointer ap, final ArithmeticExpression arg) {
		assert ap != null;
		return arg == null
				? ap					// exp := array
				: ap.endDimension(arg);	// exp := array[arg]...[]
	}
	
	/**
	 * @param asn
	 * @return an AST-based (array) pointer if available.
	 */
	public static Pointer from(final Assignable<?> asn) {
		if (asn == null) throwNullArgumentException("assignable");
		return asn.isArray()
				? fromEnclosing(asn)
				: null;
	}

	public static Pointer fromEnclosing(final Assignable<?> asn) {
		if (asn == null) throwNullArgumentException("assignable");

		final IASTArraySubscriptExpression exp = 
				asn.getEnclosingArraySubscriptExpression();
		final Pointer ap = exp != null
				? fromRecursively(exp, asn.getRuntimeAddress(), asn.getCondGen())
						: from(asn.getPathVariablePlaceholder(), (IASTArrayDeclarator) asn.getDeclarator());
				if (ap == null) throwTodoException("unsupported array");
//		ap.setAssigned(asn);
		return ap;
					
//		try {
//		} catch (NoSuchVersionException e) {
//			// thrown by asn.getPathVariablePlaceholder() and not always indicating a non-array
//			return throwUnhandledException(e);
//		}
		
		// TODO: dereferenced array
//		if (exp == null) exp = ASTAssignableComputer.isLikeAssignment(clause);
	}
	
	/**
	 * Parsing array instances, where post-fix subscript operator parsing is 
	 * de-array.
	 * 
	 * @param exp
	 * @param condGen
	 * @return
	 */
	public static Pointer fromRecursively(
			IASTArraySubscriptExpression exp, final ASTAddressable rtAddr, VODCondGen condGen) 
					throws ASTException, UncertainException {
		if (exp == null) throwNullArgumentException("expression");
		
		Pointer ap = CACHE.get(exp);
		if (ap != null) return ap;

		setArrayASTInParsing(exp);
		try {
		final Expression e = Expression.fromRecursively(
				exp.getArrayExpression(), rtAddr, condGen);

		setArrayASTInParsing(null);
		final ArithmeticExpression arg = (ArithmeticExpression) 
				Expression.fromRecursively(exp.getArgument(), rtAddr, condGen);

		assert e != null;	// after array parsing
		if (e instanceof ArrayPointer) {
			ap = from((ArrayPointer) e, arg);
			
		} else if (e instanceof PathVariablePlaceholder) {		// exp := ID[arg]...[] => ID[arg] = pvd
			ap = from((PathVariablePlaceholder) e, arg);
			
		} else ap = PointerType.NULL;
		} catch (ClassCastException ex) {	// throws ASTException, UncertainConditionException 
			throwTodoException(ex);
		}
		
		CACHE.put(exp, ap);
		return ap;
	}

	

//	private static Stack<IASTArraySubscriptExpression> getArrayASTs(
//			IASTArraySubscriptExpression subArray) {
//		if (arrayASTsInParsing == null) return null;
//		if (arrayASTsInParsing.contains(subArray)) return arrayASTsInParsing;
//		
//		for (Stack<IASTArraySubscriptExpression> array : ALL_ARRAYS.keySet()) 
//			if (!array.equals(arrayASTsInParsing) && array.contains(subArray)) return array;
//		return null;
//	}
	
	private static void setArrayASTInParsing(IASTArraySubscriptExpression parsedArray) {
		if (parsedArray == null) {
			isParsingArrayArgument = true;
			if (!arrayASTsInParsing.isEmpty()) arrayASTsInParsing.pop();
		} else {
			isParsingArrayArgument = false;
			arrayASTsInParsing.push(parsedArray);
		}
	}
	
	public static IASTArraySubscriptExpression getSubArrayInParsing() {
		if (isParsingArrayArgument) return null;
		return (!arrayASTsInParsing.isEmpty()) ? arrayASTsInParsing.peek() : null;
	}
	
	
	
	/**
	 * @return @NotNull
	 */
	public List<ArithmeticExpression> getArguments() {
		final List<ArithmeticExpression> args = new ArrayList<>();
		final ArithmeticExpression np = nextPointing();
		if (np instanceof ArrayPointer) 
			args.addAll(((ArrayPointer) np).getArguments());
		
		if (index != null) args.add(index);
		return args;
	}
	
//	@Override
//	public Pointable getPointTo() {
//		return this; 
//	}
//
//	public Pointable getDepointTo() {
//		return super.getPointTo();
//	}

//	@Override
//	public ArrayPointer getPointingBeginning() {
////		if (index instanceof Expression) 
////			for (PathVariablePlaceholder pvp : ((Expression) index).getDirectPathVariablePlaceholders())
////				asn = pvp.getAssignable();
//		final List<IASTArraySubscriptExpression> enclosings = getNonNull(()->
//				ASTUtil.getEnclosingArraySubscriptsOf(
//						getBeginningPlaceholder().getAssignable().getTopNode()));
//		if (enclosings.isEmpty()) throwTodoException("non-AST array");
//		return (ArrayPointer) fromRecursively(enclosings.get(enclosings.size() - 1), getCondGen());
//	}

	@Override
	public IASTStatement getPrivatizingBlock() {
		IASTStatement pb = super.getPrivatizingBlock(),
				ipb = index == null ? null : index.toExpression().getPrivatizingBlock();
		if (pb == null) pb = ipb;
		else if (pb != ipb && ipb != null) 
			throwTodoException("inconsistent privatizing blocks");
		return pb;
	}

	@Override
	public FunctionallableRole getThreadRole() {
		return ThreadRoleMatchable.getThreadRole(nextPointing(), getIndex());
	}

	@SuppressWarnings("unchecked")
	@Override
	public FunctionalPathVariable getVariable() {
		return FunctionalPathVariable.from((Assignable<FunctionalPathVariable>) getAssignable());
	}
	
	@Override
	public java.lang.String getID(SerialFormat format) {
		return getBeginningPlaceholder().getID(format);
	}

//	public Number<?> getZero() {
//		assert getTopPlaceholder() != null;
//		return getTopPlaceholder().getZero();
//	}
	
	public ArithmeticExpression getIndex() {
		return index;
//		return getEnd() == this ? null : index;
	}
	
	/**
	 * @param i - null means array head pointer
	 */
	public void setIndex(ArithmeticExpression i) {
//		if (i == null) throwNullArgumentException("index");
		index = i;
	}
	
	
	
	/**
	 * Adding <code>e</code> means next-pointing <code>e</code>.
	 */
	@Override
	protected boolean add(Collection<Expression> oprds, Expression e) {
//		final ArithmeticExpression np = nextPointing();
//		boolean result = super.add(oprds, e) & (np.derives(e) | e.derives(np));
		boolean result = super.add(oprds, e);
		// the initial ArrayAccessVersion doesn't exist under initial next-pointed PVP
		if (!result && e instanceof ArrayAccessVersion) 
			result = getIndex().derives(((ArrayAccessVersion<?>) e).getArguments());
		if (!result) throwTodoException("underivable operand");
		return result;
	}
	
	/**
	 * For an array instance to expand its end and dimension to the last subscript:
	 * 
	 * end = a[i] => end = a[i][j] = *(*(a+i)+j) and
	 * &end = &a[i][j] = *(a+i)+j
	 * 
	 * @param j
	 * @return
	 */
	public ArrayPointer endDimension(ArithmeticExpression j) {
		try {
			return new ArrayPointer(this, j);
			
		} catch (UnsupportedOperationException | NoSuchVersionException e) {
			return throwUnhandledException(e);
		}
	}

	
	
	@Override
	public Boolean isAssigned() {
		return getBeginningPlaceholder().isAssigned();
	}

	@Override
	public boolean isEmpty() {
		return index == null && super.isEmpty();
	}

//	/**
//	 * @return True if this is a {@link #NULL} pointer or points to nothing (null).
//	 */
//	public boolean isNull() {
//		TODO? return toProposition() contains Equality to Null;
//	}

	@Override
	public boolean isZ3ArrayAccess() {
		return getPointingBeginning().isZ3ArrayAccess();
	}
	
	

//	@Override
//	public boolean derives(ThreadRoleMatchable matchable2) {
//		return super.derives(matchable2);
//	}

	@Override
	public Boolean dependsOn(Expression e) {
		if (index != null) {
			if (index instanceof Expression) {
				if (tests(((Expression) index).dependsOn(e))) return true;
			} else 
				throwTodoException("unsupported index type");
		}
		return super.dependsOn(e);
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
		final ArrayPointer newCe = (ArrayPointer) super.cloneReversion(blockStat, role, ver);
		if (newCe == this) return (T) this;
		
		if (index != null) newCe.index = index.cloneReversion(blockStat, role, ver);
		return (T) newCe;
	}

	
	
	@Override
	protected <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType) {
		final Set<T> dvrs = new HashSet<>(super.cacheDirectVariableReferences(refType));
		for (ArithmeticExpression arg : getArguments()) 
			dvrs.addAll(arg.toExpression().getDirectVariableReferences(refType));
		return dvrs;
	}

	@Override
	protected Set<Function> cacheDirectFunctionReferences() {
		final Set<Function> dfrs = new HashSet<>(super.cacheDirectFunctionReferences());
		for (ArithmeticExpression arg : getArguments()) 
			dfrs.addAll(arg.toExpression().getDirectFunctionReferences());
		return dfrs;
	}
	
	@Override
	protected Function cacheFunctionScope() {
		return getBeginningPlaceholder().getFunctionScope(); 
//				TODO: merging ((ConditionElement) index).getFunctionScope();
	}
	

	
	@Override
	protected boolean equalsToCache(SystemElement e2) {
		if (!super.equalsToCache(e2)) return false;
		
		final ArrayPointer a2 = (ArrayPointer) e2;
		ArithmeticExpression idx2 = a2.index;
		if (index == null && idx2 != null) return false;
		if (index != null && !index.equals(idx2)) return false;
		
		final ArithmeticExpression b1 = nextPointing(), b2 = a2.nextPointing();
		if (b1 == this) return b2 == a2 && 
				getBeginningPlaceholder().equals(a2.getBeginningPlaceholder());
		return b1.equals(b2); 
	}
	
	@Override
	protected List<Integer> hashCodeVars() {
		final List<Integer> hcvs = new ArrayList<>(super.hashCodeVars());
		hcvs.add(index == null ? 0 : index.hashCode()); 
		return hcvs;
	}

	

	public boolean hasIteratingArgumentsFrom(IASTStatement loop) 
			throws ASTException, IncomparableException, 
			UncertainPlaceholderException, NoSuchVersionException {
		if (loop instanceof IASTForStatement)
			return hasIteratingArgumentsFrom((IASTForStatement) loop);
		return throwTodoException("unsupported loop");
	}
	
	public boolean hasIteratingArgumentsFrom(IASTForStatement loop) 
			throws ASTException, IncomparableException, 
			UncertainPlaceholderException, NoSuchVersionException {
		if (loop == null) throwNullArgumentException("loop");
		final Assignable<?> it = Assignable.fromCanonicalIteratorOf(
				loop, cacheRuntimeAddress(), getCondGen());
		for (ArithmeticExpression arg : getArguments())
			for (PathVariablePlaceholder argPvp : arg.getDirectPathVariablePlaceholders())
				if (it.equalsVariable(argPvp)) return true;
		return false;
	}
	
	
	
//	public ArithmeticExpression add(ArithmeticExpression addend) {
//		return getPointToEnd().add(addend);
//	}
//	
//	public ArithmeticExpression subtract(ArithmeticExpression addend) {
//		return getPointToEnd().subtract(addend);
//	}
//	
//	public ArithmeticExpression multiply(ArithmeticExpression addend) {
//		return getPointToEnd().multiply(addend);
//	}
//	
//	public ArithmeticExpression divide(ArithmeticExpression addend) {
//		return getPointToEnd().divide(addend);
//	}


	
	@SuppressWarnings("unchecked")
	@Override
	public <T extends Addressable> T previous() {
		return (T) applySkipNull(pAsn-> from(pAsn),
				()-> getAssignable().previous());
	}
	
//	@SuppressWarnings("unchecked")
//	@Override
//	public <T extends Addressable> NavigableSet<T> previousRuntimes() {
//		final NavigableSet<T> prs = new TreeSet<>();
//		final Assignable pAsn = getAssignable().previousRuntimes();
//		if (pAsn == null) return null;
//		if (pAsn.isArray()) return (T) pAsn.getEnclosingArray();
//		if (pAsn.isPointer()) return (T) pAsn.getEnclosingPointer();
//		return throwTodoException("unsupported previous runtime");
//	}
	

	
	@Override
	@SuppressWarnings("unchecked")
	public <T extends ConditionElement> T substitute(
			Reference<?> ref1, Reference<?> ref2) {
		if (super.substitute(ref1, ref2) != this)
			throwTodoException("inconsistent array substitution");
		
		if (index != null && nextPointing() == ref2) try {
			if (ref2 instanceof VariablePlaceholder<?>)
				index = ((ArrayAccessVersion<?>) ((VariablePlaceholder<?>) ref2).getVersion()).getAstArgument(0);
			else
				throwTodoException("unsupported next pointing");
		} catch (ClassCastException e) {
			throwTodoException(e);
		}
		return (T) this;
	}

	
	
	@Override
	public java.lang.String toNonEmptyString(boolean usesParenAlready) {
		assert getOp() == Operator.Depoint; 
		return nextPointing().toNonEmptyString() + "[" + (index == null ? "" : index.toString()) + "]";
//		return getID(null) + "[" + (index == null ? "" : index.toString()) + "]";
	}

	/**
	 * For array type and instance reading.
	 * 
	 * @see ompca.condition.data.Pointer#toZ3SmtString(boolean, boolean, boolean)
	 */
	@Override
	public java.lang.String toZ3SmtString(
			boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs) {
		// ArrayAccessVersion is saved on the beginning (placeholder)
//		final ArrayAccessVersion ver = getNonNull(()-> getBeginningPlaceholder())
//				.getVersion(ArrayAccessVersion.class);
//		if (ver == null) throwTodoException("array doesn't have an AAV");
//		return ver.toZ3SmtString(
//				printsVariableDeclaration, printsFunctionDefinition);	
		return getNonNull(()-> getPointingBeginning()).toZ3SmtString(
				printsVariableDeclaration, printsFunctionDefinition, isLhs);	
	}
	
//	/**
//	 * For array instance writing only.
//	 * 
//	 * @param valueToStore
//	 * @return
//	 * @see ompca.condition.version.ArrayAccessVersion#toZ3SmtString(boolean, boolean)
//	 */
//	public java.lang.String toZ3SmtString(Expression valueToStore) {
//		final Expression np = nextPointing().toExpression();
//		if (!np.isArray()) return null;
//	}

}