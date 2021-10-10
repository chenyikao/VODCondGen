/**
 * 
 */
package ompca.vodcg;

import java.lang.reflect.Method;
import java.util.AbstractSet;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NavigableSet;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.function.Predicate;
import java.util.function.Supplier;

import org.eclipse.cdt.core.dom.IName;
import org.eclipse.cdt.core.dom.ast.ASTNameCollector;
import org.eclipse.cdt.core.dom.ast.IASTArrayDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTDoStatement;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFieldReference;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTInitializer;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNameOwner;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTReturnStatement;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.core.dom.ast.IBinding;
import org.eclipse.cdt.core.dom.ast.IFunction;
import org.eclipse.cdt.core.dom.ast.IMacroBinding;
import org.eclipse.cdt.core.dom.ast.IQualifierType;
import org.eclipse.cdt.core.dom.ast.IType;
import org.eclipse.cdt.core.dom.ast.IVariable;
import org.eclipse.core.runtime.SubMonitor;

import ompca.Addressable;
import ompca.DuoKeyMap;
import ompca.Elemental;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.AssignableExpression;
import ompca.vodcg.condition.Expression;
import ompca.vodcg.condition.ExpressionRange;
import ompca.vodcg.condition.Function;
import ompca.vodcg.condition.FunctionCall;
import ompca.vodcg.condition.FunctionalPathVariable;
import ompca.vodcg.condition.ParallelCondition;
import ompca.vodcg.condition.PathCondition;
import ompca.vodcg.condition.PathVariable;
import ompca.vodcg.condition.PathVariablePlaceholder;
import ompca.vodcg.condition.Proposition;
import ompca.vodcg.condition.SideEffectElement;
import ompca.vodcg.condition.VODConditions;
import ompca.vodcg.condition.VariablePlaceholder;
import ompca.vodcg.condition.data.ArrayPointer;
import ompca.vodcg.condition.data.DataType;
import ompca.vodcg.condition.data.PlatformType;
import ompca.vodcg.condition.data.Pointer;
import ompca.vodcg.condition.data.PointerType;
import ompca.vodcg.condition.version.FunctionalVersion;
import ompca.vodcg.condition.version.FunctionallableRole;
import ompca.vodcg.condition.version.NoSuchVersionException;
import ompca.vodcg.condition.version.ThreadRole;
import ompca.vodcg.condition.version.ThreadRoleMatchable;
import ompca.vodcg.condition.version.Version;
import ompca.vodcg.condition.version.VersionEnumerable;
import ompca.vodcg.parallel.OmpDirective;
import ompca.vodcg.parallel.ThreadPrivatizable;

/**
 * {@link org.eclipse.cdt.core.dom.ast.IASTExpression#isLValue} does NOT guarantee 
 * all left hand side assignables are included!
 * 
 * Hence an l-value may be just a declarator binding, {@link IASTName}, an ID expression, 
 * a pointer expression or a reference expression. Which is NOT necessarily assigned 
 * but is potentially assignable.
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class Assignable<PV extends PathVariable> extends SystemElement 
//TODO? implements Type-able
implements VersionEnumerable<PV>, ThreadPrivatizable, Comparable<Assignable<?>>, Comparator<Assignable<?>> {
	
	private interface AssignableProcessable {
		boolean test(Assignable<?> lv); //throws DOMException, InterruptedException, CoreException;
	}
	
	private class AssignableProcessor extends AbstractSet<Assignable<?>> {
		private Set<Assignable<?>> unprocessedLvs;
		
//		IASTNode lastOvrBranch = null;
		int i = 0;	// for forEach loop numerical indexing
		
		AssignableProcessor(Set<Assignable<?>> lvs) {
			assert lvs != null;
			unprocessedLvs = lvs;
		}
		
		public Exception forEach(AssignableProcessable action) {
			return forEach(toPredicate(action));
		}
		
		public Exception forEach(Predicate<? super Assignable<?>> action) {
			if (action == null) throwNullArgumentException("action");
			
			Exception re = null;
			int lastIncompletesCount = 0, incompletesCount;
			while (true) {
				i = 0; incompletesCount = 0;
				for (Assignable<?> rhs : this) {
					try {
//						if (!processedRhs.contains(rhs)) {
//							processedRhs.push(rhs);
							if (!action.test(rhs)) incompletesCount++;
//							if (processedRhs.pop() != rhs) throwTodoException("Not a stack");
//						}
					} catch (ReenterException e) {
						continue;
					} catch (UncertainPlaceholderException e) {
						throw e;
					} catch (UncertainException | IncomparableException | ASTException e) {
						re = e;
						incompletesCount++;
					}
					i++;
				}
				// checking the completeness of OV only after ALL its assigners are processed
				if (incompletesCount == 0) return null;
				if (lastIncompletesCount == incompletesCount) return re;	//throwTodoException("endless rhs processing");
				lastIncompletesCount = incompletesCount;
			}
		}

		/* (non-Javadoc)
		 * @see java.util.AbstractCollection#add(java.lang.Object)
		 */
		@Override
		public boolean add(Assignable<?> lv) {
			return unprocessedLvs.add(lv);
		}
		
		/* (non-Javadoc)
		 * @see java.util.AbstractCollection#iterator()
		 */
		@Override
		public Iterator<Assignable<?>> iterator() {
			return unprocessedLvs.iterator();
		}

		/* (non-Javadoc)
		 * @see java.util.AbstractCollection#size()
		 */
		@Override
		public int size() {
			return unprocessedLvs.size();
		}
		
		public Predicate<? super Assignable<?>> toPredicate(AssignableProcessable action) {
			return lv -> {
//				try {
					return action.test(lv);
//				} catch (DOMException | InterruptedException | CoreException e) {
//					e.printStackTrace();
//				}
			};
		}
	}
	

	
	/**
	 * In case {@link nameView} could be null.
	 */
	private static final Map<IBinding, Map<IASTName, Assignable<?>>> 
	ASSIGNABLE_CACHE = new HashMap<>();

	// caching comparison results
	private static final DuoKeyMap<Assignable<?>, Assignable<?>, Integer> 
	COMPARE_CACHE = new DuoKeyMap<>();
	
	private static final Map<IASTForStatement, Assignable<?>> 
	LOOP_ITERATOR_CACHE = new HashMap<>();
//	private static final Map<IASTForStatement, Trio<Assignable, Assignable, Assignable>> 
//	LOOP_ITERATOR_CACHE = new HashMap<>();
	
	private static final Method METHOD_CACHE_CONSTANT = 
			Elemental.getMethod(Assignable.class, "cacheConstant");
	private static final Method METHOD_IS_ASSIGNED = 
			Elemental.getMethod(Assignable.class, "isAssigned");
	private static final Method METHOD_IS_CONDITIONAL_TO = 
			Elemental.getMethod(Assignable.class, "isConditionalTo", IASTForStatement.class);
	private static final Method METHOD_IS_FUNCTIONAL = 
			Elemental.getMethod(Assignable.class, "isFunctional");
	private static final Method METHOD_GET_CONDITIONS = 
			Elemental.getMethod(Assignable.class, "getConditions", String.class);
	private static final Method METHOD_GET_PARALLEL_CONDITION = 
			Elemental.getMethod(Assignable.class, "getParallelCondition");
//	private static final Method 
//	METHOD_GET_PATH_VARIABLE = Elemental.getMethod(Assignable.class, "getPathVariable");
//	private static final Method 
//	METHOD_GET_PATH_VARIABLE_DELEGATE = Elemental.getMethod(Assignable.class, "getPathVariableDelegate");
//	private static final Method 
//	METHOD_SET_PATH_VARIABLE_DELEGATE = Elemental.getMethod(Assignable.class, "setPathVariableDelegate");

	private IBinding bindingView;
	private IASTName nameView;
	private IASTNameOwner nameOwnerView;
	private IASTExpression expView;
	private Assignment firstAssignmentView;

	// for cache/registry on demand
	private List<IASTStatement> 		branches = null;
	private Proposition			 		branchCond = null;
	private Assignable<PV>				previous = null;	
	private final Set<Assignable<?>> 	assigners = new HashSet<>();	
//	private Boolean isAssigning = null;
	private Boolean isAssigned = null;
//	private boolean completesGenCond = false;
	
	private SubMonitor monitor = null; 
	private int workLeft = 0;

	static private ASTRuntimeLocationComputer ALC = null; 

	
	
	/**
	 * L-value comes from a declarator binding (assignment) of (external) libraries.
	 * 
	 * @param var
	 */
	private Assignable(IVariable var, VODCondGen condGen) {
		super(null, condGen);
		
		assert var != null;
		init(var, null, null, null);
	}

	/**
	 * L-value comes from an assignment as an IASTNameOwner in either an IASTDeclarator or an IASTIdExpression.
	 * 
	 * @param name
	 * @param bind - pre-cached name (variable) binding if there is one.
	 * @param owner - pre-cached name owner if there is one.
	 * @param condGen 
	 */
	protected Assignable(
			IASTName name, IBinding bind, IASTNameOwner owner, final ASTAddressable rtAddr, VODCondGen condGen) {
		super(rtAddr, condGen);
		
		assert name != null && owner == name.getParent();
//		if (name.isDefinition()) VAR_DEFINITION_CACHE.put
		init(bind == null ? name.resolveBinding() : bind, name, owner, rtAddr);
		
		// assert (parent != null && parent instanceof IASTDeclarator)
		if (owner instanceof IASTDeclarator) expView = null;
		
		// assert (parent != null && parent instanceof IASTIdExpression)
		else if (owner instanceof IASTIdExpression) {
			IASTNode parent = (IASTNode) owner;
			while (true) {
				expView = (IASTExpression) parent;
				parent = parent.getParent();
				if (parent != null && parent instanceof IASTUnaryExpression) {
					int parentOp = ((IASTUnaryExpression) parent).getOperator();
					if (parentOp != IASTUnaryExpression.op_amper 
							&& parentOp != IASTUnaryExpression.op_bracketedPrimary
							&& parentOp != IASTUnaryExpression.op_star) break;
				} else break;
			}
			assert expView.isLValue();
		} 
		else if (owner instanceof IASTFieldReference) 
			expView = ((IASTFieldReference) owner).getFieldOwner();
			
		else if (owner instanceof IASTExpression)
			expView = (IASTExpression) owner;
		
		else throwIllegalNameException(name);
	}

	private void init(final IBinding bind, final IASTName name, final IASTNameOwner nameOwner, 
			final ASTAddressable rtAddr) {
		if (name != null && name.getFileLocation() != null && rtAddr != null) throwTodoException("inconsistent addresses");
		
		bindingView = bind;
		nameView = name;
		nameOwnerView = nameOwner;
		firstAssignmentView = null;
		
		final VODCondGen cg = getCondGen();
		assert cg != null;
		if (ALC == null) ALC = new ASTRuntimeLocationComputer(cg);
		monitor = cg.splitMonitor();
		assert monitor != null;
	}
	
	public ThreadRole initRole() {
		if (tests(isConstant())) return ThreadRole.CONST;
//		if (isArray()) return ArrayPointer.from(this).getThreadRole();
		if (isLoopIterator() || isThreadPrivate() || tests(isDirectlyFunctional())) return ThreadRole.FUNCTION;
		return ThreadRole.MASTER;
	}
	

	
//	private static Assignable<?> fromCache(IBinding asnBind, Supplier<Assignable<?>> asnSup) {
//		assert asnSup != null;
//	}
	
	/**
	 * @param asnName
	 * @param asnBind - the pre-cached L-value must be a writable binding: a variable or a function, 
	 * if available
	 * @param asnNameOwner
	 * @param condGen 
	 * @return
	 */
	private static Assignable<?> fromCache(IASTName asnName, 
			IBinding asnBind, IASTNameOwner asnNameOwner, final ASTAddressable rtAddr, VODCondGen condGen) 
					throws ASTException {
		if (asnBind == null) throwNullArgumentException("binding");
		
		Map<IASTName, Assignable<?>> varBindLvs = ASSIGNABLE_CACHE.get(asnBind);
		Assignable<?> asn = null;
		
		if (varBindLvs == null) 
			ASSIGNABLE_CACHE.put(asnBind, varBindLvs = new HashMap<>());
		else asn = varBindLvs.get(asnName);
		if (asn != null) return asn;
		
		if (asnName != null && asnNameOwner == null) {
			IASTNode varNameParent = asnName.getParent();
			if (varNameParent instanceof IASTNameOwner) 
				asnNameOwner = (IASTNameOwner) varNameParent;
		}
		
		varBindLvs.put(asnName, asn = asnBind instanceof IFunction 
				? new FunctionAssignable(asnName, (IFunction) asnBind, asnNameOwner, rtAddr, condGen) 
				: (asnName == null 
						? new Assignable<>((IVariable) asnBind, condGen) 
						: new Assignable<>(asnName, asnBind, asnNameOwner, rtAddr, condGen)));
		final Assignable<?> asn_ = asn;
		return get(()-> asn_.toFunctional(),
				()-> asn_);
	}

	/**
	 * @param var
	 * @param condGen 
	 * @return
	 */
	public static Assignable<?> from(IVariable var, VODCondGen condGen) {
		return fromCache(null, var, null, null, condGen);
	}

	/**
	 * @param name
	 * @param nameOwner - pre-cached name owner if there is one.
	 * @param condGen 
	 * @return
	 */
	public static Assignable<?> from(
			IASTName name, IASTNameOwner nameOwner, final ASTAddressable rtAddr, VODCondGen condGen) 
					throws ASTException {
		if (name == null) throwNullArgumentException("AST name");
		
		IBinding lvBind = name.resolveBinding();
		// L-value must be a assignable binding: a variable or a function 
		return isAssignableBinding(lvBind) 
				? fromCache(name, lvBind, nameOwner, rtAddr, condGen) : null ;
	}
	
	/**
	 * @param varName
	 * @param condGen 
	 * @return
	 */
	public static Assignable<?> from(IASTName varName, final ASTAddressable rtAddr, VODCondGen condGen) 
			throws ASTException {
		return from(varName, null, rtAddr, condGen);
	}
	
	/**
	 * @param nameOwner
	 * @param condGen 
	 * @return
	 */
	public static Assignable<?> from(IASTNameOwner nameOwner, final ASTAddressable rtAddr, VODCondGen condGen) {
		return nameOwner != null 
				? from(ASTUtil.getNameOf(nameOwner), nameOwner, rtAddr, condGen) 
				: throwNullArgumentException("AST name owner");
	}
	
	/**
	 * @param lvBind - the pre-cached L-value must be a assignable binding: 
	 * 	a variable or a function, 
	 * if available
	 * @param lvName
	 * @param lvNameOwner
	 * @param condGen
	 * @return
	 */
	public static Assignable<?> from(IBinding lvBind, 
			IASTName lvName, IASTNameOwner lvNameOwner, final ASTAddressable rtAddr, VODCondGen condGen) {
		if (lvName == null) throwNullArgumentException("name");
		
		if (lvBind == null) return from(lvName, rtAddr, condGen);
		return isAssignableBinding(lvBind) 
				? fromCache(lvName, lvBind, lvNameOwner, rtAddr, condGen) : null ;
	}
	
	public static Assignable<?> from(
			final IASTInitializerClause clause, final ASTAddressable rtAddr, VODCondGen condGen) 
					throws ASTException {
		if (clause == null) throwNullArgumentException("clause");
		
		final IASTNameOwner no = ASTAssignableComputer.getVariableNameOwnerOf(clause);
		if (no != null) return from(no, rtAddr, condGen);
		
		final IASTName name = ASTAssignableComputer.getVariableNameOf(clause);
		return name != null ?
				from(name, rtAddr, condGen) : null;
	}

	public static Assignable<?> from(
			IName varName, boolean refreshesIndex, VODCondGen condGen) {
		if (varName == null) throwNullArgumentException("variable name");
		return from(
				ASTUtil.getNameFrom(varName.getFileLocation(), refreshesIndex), 
				null,
				condGen);
	}
	
//	/**
//	 * @param lv - needing L-value checking
//	 * @return
//	 */
//	public static LValue from(IASTExpression lv) {
//		return ??;
//	}

	/**
	 * @param root
	 * @param condGen
	 * @return @NotNull a sorted and navigable assignable set.
	 */
	public static NavigableSet<Assignable<?>> fromOf(
			IASTNode root, final ASTAddressable rtAddr, VODCondGen condGen) {
		if (root == null) throwNullArgumentException("root node");

		NavigableSet<Assignable<?>> asns = null;
		if (root instanceof IASTName) {
			final Assignable<?> asn = from((IASTName) root, rtAddr, condGen);
			asns = new TreeSet<>(asn);
			asns.add(asn);
			return asns;
		}
		
		final IASTNode[] children = root.getChildren();
		if (children != null) for (IASTNode child : children) {
			final NavigableSet<Assignable<?>> subAsns = fromOf(child, rtAddr, condGen);
			if (subAsns.isEmpty()) continue;
			if (asns == null) asns = new TreeSet<>(subAsns);
			else asns.addAll(subAsns);
		}
		return asns == null
				? Collections.emptyNavigableSet()
				: asns;
	}
	
	/**
	 * @param root
	 * @param name
	 * @param condGen
	 * @return a sorted and navigable assignable set.
	 */
	public static NavigableSet<Assignable<?>> fromOf(
			IASTNode root, IASTName name, final ASTAddressable rtAddr, VODCondGen condGen) {
		return name == null
				? fromOf(root, rtAddr, condGen)
				: fromOf(root, String.valueOf(name.getSimpleID()), rtAddr, condGen);
//		return fromOf(root, name.toString(), condGen);
	}
	
	/**
	 * @param root
	 * @param name
	 * @param condGen 
	 * @return a sorted and navigable assignable set.
	 */
	public static NavigableSet<Assignable<?>> fromOf(IASTNode root, String name, final ASTAddressable rtAddr, VODCondGen condGen) {
		if (root == null) throwNullArgumentException("root AST node");
		if (name == null) throwNullArgumentException("name");
		
		// org.eclipse.cdt.core.dom.ast.ASTNameCollector may be less efficient then the index tree,
		//	if either getReferences(...) or findReferences(...) could work!
		final ASTNameCollector nameCollector = new ASTNameCollector(name);
		root.accept(nameCollector);
		
		NavigableSet<Assignable<?>> asns = null;
		for (IASTName ref : nameCollector.getNames()) {
			final Assignable<?> asn = from(ref, rtAddr, condGen);
			if (asns == null) asns = new TreeSet<>(asn);
			asns.add(asn);
		}
		return asns == null
				? Collections.emptyNavigableSet()
				: asns;
	}

	

	/**
	 * By definition the increment iterates loop and getting the iterator from increment avoids 
	 * complex initializers.
	 * 
	 * <pre>
	 *	for (init-expr; test-expr; incr-expr) structured-block
	 * 		init-expr 	One of the following:
	 * 					var = lb
	 * 					integer-type var = lb
	 * 					random-access-iterator-type var = lb
	 * 					pointer-type var = lb
	 * 
	 *		var 		One of the following:
	 *						A variable of a signed or unsigned integer type.
	 *						TODO: For C++, a variable of a random access iterator type.
	 *						TODO: For C, a variable of a pointer type.
	 *					If this variable would otherwise be shared, it is implicitly made private in the
	 *					loop construct. This variable must not be modified during the execution of the
	 *					for-loop other than in incr-expr. Unless the variable is specified lastprivate
	 *					or linear on the loop construct, its value after the loop is unspecified.
	 * 
	 *		lb and b 	Loop invariant expressions of a type compatible with the type of var.
	 *<br>
	 *
	 * @param loop
	 * @param condGen 
	 * @return
	 */
	public static Assignable<?> fromCanonicalInitializedIteratorOf(IASTForStatement loop, final ASTAddressable rtAddr, VODCondGen condGen) {
		return Assignment.from(loop, rtAddr, condGen).getAssigned();
	}
			
	/**
	 * @param loop
	 * @param condGen
	 * @return The iterating iterator of <code>loop</code>.
	 */
	public static Assignable<?> fromCanonicalIteratorOf(IASTForStatement loop, final ASTAddressable rtAddr, VODCondGen condGen) {
		if (ASTLoopUtil.isNonCanonical(loop)) throwTodoException("non-canonical loop");
		
		Assignable<?> li = LOOP_ITERATOR_CACHE.get(loop);
		if (li == null) {
			final IASTExpression lie = ASTLoopUtil.getCanonicalIteratorOf(loop);
			if (lie != null) LOOP_ITERATOR_CACHE.put(loop, li = from(lie, rtAddr, condGen));
			else ASTLoopUtil.setNonCanonical(loop);
		}
		return li;
		
		//		IASTName iv;
		
		/* TODO:
		 * 	The canonical form allows the iteration count of all associated loops to be computed before
		 * 	executing the outermost loop. The computation is performed for each loop in an integer type. This
		 * 	type is derived from the type of var as follows:
		 * 
		 * 		�� 	If var is of an integer type, then the type is the type of var.
		 * 		�� 	TODO: For C++, if var is of a random access iterator type, then the type is the type that 
		 * 			would be used by std::distance applied to variables of the type of var.
		 * 		�� 	TODO: For C, if var is of a pointer type, then the type is ptrdiff_t.
		 * 
		 * 	The behavior is unspecified if any intermediate result required to compute the iteration count
		 * 	cannot be represented in the type determined above.
		 * 
		 * 	There is no implied synchronization during the evaluation of the lb, b, or incr expressions. It is
		 *  unspecified whether, in what order, or how many times any side effects within the lb, b, or incr
		 *	expressions occur.
		 *
		 *	Note �� Random access iterators are required to support random access to elements in constant
		 *	time. Other iterators are precluded by the restrictions since they can take linear time or offer 
		 *	limited functionality. It is therefore advisable to use tasks to parallelize those cases.
		 *
		 *	Restrictions
		 *	
		 *	The following restrictions also apply:
		 *	
		 *		�� 	If test-expr is of the form var relational-op b and relational-op is < or <= then incr-expr 
		 *			must cause var to increase on each iteration of the loop. If test-expr is of the form 
		 *			'var relational-op b' and relational-op is > or >= then incr-expr must cause var to decrease 
		 *			on each iteration of the loop.
		 *		�� 	If test-expr is of the form 'b relational-op var' and relational-op is < or <= then incr-expr 
		 *			must cause var to decrease on each iteration of the loop. If test-expr is of the form 
		 *			'b relational-op var' and relational-op is > or >= then incr-expr must cause var to increase 
		 *			on each iteration of the loop.
		 *		�� 	TODO: For C++, in the simd construct the only random access iterator types that are allowed 
		 *			for var are pointer types.
		 *		�� 	The b, lb and incr expressions may not reference var of any of the associated loops.
		 */
	}
	
	private static void throwIllegalNameException(IASTName name) {
		throw new IllegalArgumentException("No assignable found for the name '" 
				+ ((name == null)?"null'":(name + "' " + ASTUtil.toStringOf(name.getFileLocation()))));
	}

	<T> T throwIncomparableException(Assignable<?> asn2) {
		return throwIncomparableException(asn2, "assignables");
	}
	
	<T> T throwIncomparableException(Assignable<?> asn2, String message, Method... callees) {
		return throwIncomparableException(asn2, message, null, callees);
	}
	
	<T> T throwIncomparableException(Assignable<?> asn2, String message, Exception cause, Method... callees) {
		if (callees != null) leave(callees);
		throw new IncomparableException(this, asn2, message, cause);
	}
	
	
	
	public <T> T throwUncertainPlaceholderException() 
			throws UncertainPlaceholderException {
		return throwUncertainPlaceholderException(null);
	}
	
	public <T> T throwUncertainPlaceholderException(Method callee) 
			throws UncertainPlaceholderException {
		return throwUncertainPlaceholderException(null, callee);
	}
	
	public <T> T throwUncertainPlaceholderException(String message, Method... callees) 
			throws UncertainPlaceholderException {
//		leave(callees);
		if (message == null) message = toString();
		return throwUncertainPlaceholderException(message, null, this, callees);
	}
	

	
	/**
	 * @param bind
	 * @return
	 */
	public static boolean isAssignableBinding(IBinding bind) {
		return bind instanceof IVariable 
				|| bind instanceof IFunction
				|| bind instanceof IMacroBinding;
	}
	
	
	
	static public Collection<Assignable<?>> getAll() {
		Collection<Assignable<?>> all = new ArrayList<>();
		for (Map<IASTName, Assignable<?>> nlvs : new ArrayList<>(ASSIGNABLE_CACHE.values()))
			for (Assignable<?> lv : new ArrayList<>(nlvs.values())) 
				all.add(lv);
		return all;
	}
	
	@Override
	public Assignable<?> getAssignable() {
		return this;
	}
	
//	static public Set<Assignable> getOnesEquals(PathVariable pv) {
//		if (pv == null) throwInvalidityException("must provide some path variable");
//		
//		Set<Assignable> ones = new HashSet<>();
//		for (Map<IASTName, Assignable> nlvs : new ArrayList<>(ASSIGNABLE_CACHE.values()))
//			for (Assignable lv : new ArrayList<>(nlvs.values())) 
//				if (lv.equalsVariable(pv)) ones.add(lv);
//		return ones;
//	}
	
	/**
	 * @return self-exclusive assignable's.
	 */
	public Set<Assignable<PV>> getOthersEqualsVariable() {
		return getOthersEqualsVariable(asn -> asn != this && equalsVariable(asn));
	}
	
	@SuppressWarnings("unchecked")
	private Set<Assignable<PV>> getOthersEqualsVariable(Predicate<Assignable<?>> tester) {
		assert tester != null;	// && tester.apply(...) != null
		final Set<Assignable<PV>> ones = new HashSet<>();
		for (Map<IASTName, Assignable<?>> nameAsns : new ArrayList<>(ASSIGNABLE_CACHE.values()))
			for (Assignable<?> asn : nameAsns.values()) 
				if (tester.test(asn)) ones.add((Assignable<PV>) asn);
		return ones;
	}
	
	public Set<Assignable<PV>> getOtherAssignedsEqualsVariable() {
		return getOthersEqualsVariable(asn -> asn != this && equalsVariable(asn) && tests(asn.isAssigned()));
	}
	
	public IBinding getBinding() {
		return bindingView;
	}
	
	public Assignable<PV> getDeclared() {
		return isDeclarator() ? 
				this : getSkipNull(()-> previous().getDeclared());
	}
	
	public IASTDeclarator getDeclarator() {
		return isDeclarator() ? 
				(IASTDeclarator) nameOwnerView : null;
	}

	public IASTExpression getExpressionView() {
		return expView;
	}
	
	public IASTName getASTName() {
		return nameView;
	}
	
	@Override
	public String getName() {
		return getNonNull(()-> getASTName().toString());
	}
	
	public IASTNameOwner getNameOwner() {
		return nameOwnerView;
	}
	
	@Override
	public PlatformType getType() {
		try {
			PlatformType t = getSkipNull(()-> DataType.from(getASTName()));
			if (t == null) t = applySkipNull(
					bind-> DataType.from(bind), ()-> getBinding());
			if (t == null) 
				throwTodoException("unknown type");
			return t;
			
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	
	
	
	@SuppressWarnings("unchecked")
	@Override
	public Version<? extends PV> peekVersion() {
		return (Version<? extends PV>) getPathVariablePlaceholder().peekVersion();
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public Version<? extends PV> peekVersion(ThreadRoleMatchable role) {
		return (Version<? extends PV>) getNonNull(()-> getPathVariablePlaceholder())
				.peekVersion(role);
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public Version<? extends PV> getVersion() {
		return (Version<? extends PV>) getPathVariablePlaceholder().getVersion();
	}
	
	/**
	 * TODO? assumed not assigned
	 * 
	 * @param role 
	 * @return an inherited version without assignment-caused reversion.
	 */
	@SuppressWarnings("unchecked")
	@Override
	public Version<? extends PV> getVersion(FunctionallableRole role) {
		return (Version<? extends PV>) getPathVariablePlaceholder().getVersion(role);
	}
	
	@Override
	public PV getVersionSubject() {
		return getPathVariable();
	}
	
	public IVariable getVariable() {
		if (nameView == null && 
				bindingView != null && 
				bindingView instanceof IVariable) return (IVariable) bindingView;
		else return null;
	}

//	@Override
//	public Set<Version<Variable>> getDirectVariableReferences() {
//		return Collections.singleton(PathVariablePlaceholder.from(this));
//	}
	
	@SuppressWarnings("unchecked")
	public PV getPathVariable() {
		// avoiding PathVariable.from(...) -> getPathVariable() cycle
		return (PV) (tests(isFunctional())
				? FunctionalPathVariable.from(toFunctional())
				: PathVariable.from((Assignable<PathVariable>) this));
	}
	
	public PathVariablePlaceholder getPathVariablePlaceholder() {
//		if (pvd == null) throwInvalidityException("missed delegate construction");
		return PathVariablePlaceholder.from(this);
	}
	
//	public PathVariableDelegate setPathVariableDelegate() {
//		if (enters(METHOD_SET_PATH_VARIABLE_DELEGATE)) return null;
//		
//		enter(METHOD_SET_PATH_VARIABLE_DELEGATE);
//		PathVariableDelegate newPvd = PathVariableDelegate.from(this);
//		leave(METHOD_SET_PATH_VARIABLE_DELEGATE);
//		
//		if (newPvd == null) throwNullArgumentException("path variable delegate");
//		else if (pvd == null) pvd = newPvd;
//		else if (pvd != newPvd) throwTodoException("setting inconsistent path variable delegates");
//		return pvd;
//	}
	
	
	
	private ParallelCondition getParallelCondition() {
		// avoiding assigned-assigner recursion
		if (enters(METHOD_GET_PARALLEL_CONDITION)) return null;
		
		enter(METHOD_GET_PARALLEL_CONDITION);
		ParallelCondition pc = null;
		if (tests(isAssigned())) {
			// direct parallel condition
			for (OmpDirective dir : getEnclosingDirectives()) {
				final ParallelCondition subPc = dir.getCondition();
				if (pc == null) pc = subPc;
				else pc.and(subPc);	// dir != null => subPc != null
			}
			// indirect parallel condition - self assigner involves only path condition
			for (Assignable<?> asnr : getAssigners()) if (asnr != this) {
				final ParallelCondition subPc = asnr.getParallelCondition();
				if (pc == null) pc = subPc;
				else if (subPc != null) pc.and(subPc);
			}
			
		} else for (VersionEnumerable<PV> pra : previousRuntimeAssigneds()) {
//			final ParallelCondition subPc = debugGet(()-> guard(
//					()-> ((Assignable<PV>) pra).getParallelCondition(),
//					()-> null));	// for loop-recursively assigned
			final ParallelCondition subPc = ((Assignable<PV>) pra).getParallelCondition();
			if (subPc != null) {
				if (pc == null) pc = subPc;
				else pc.or(subPc);
			}
		}
		leave(METHOD_GET_PARALLEL_CONDITION);

		return pc;
	}
	
	/**
	 * The path condition of canonical loop iterating (index++/--)
	 * is interested by <em>only</em> functional expressions.
	 * 
	 * @return null for a loop iterator.
	 * @throws ASTException
	 */
	private PathCondition getPathCondition() throws ASTException {
		if (isLoopIterator()) return null;

		if (tests(isAssigned())) 
			return PathCondition.from(getFirstAssignment().toEquality());
			
		else {
			PathCondition pc = null;
			for (VersionEnumerable<PV> pra : previousRuntimeAssigneds()) {
				final PathCondition subPc = ((Assignable<PV>) pra).getPathCondition();
				if (subPc != null) {
					if (pc == null) pc = subPc;
					else pc.or(subPc);
				}
			}
			return pc;
		}
	}
	
	private VODConditions getAssignmentConditions(final String progress) 
			throws IncomparableException, ASTException {
		log(progress, "traversing WH of " + this);
		
		//	ii. for each expression E of WRS :
//		if (ovRef.isLoopIterator()) continue;
		final VODCondGen cg = getCondGen();	
		final Assignment asm = getFirstAssignment();	
		assert asm != null;
		VODConditions condAntec = new VODConditions(getParallelCondition(), getPathCondition(), cg), 
				condConsq = new VODConditions(getRuntimeAddress(), cg);
		
		Set<Assignable<?>> asnrs = null;
		try { 
			asnrs = getAssigners();
		} catch (UncertainPlaceholderException e) {
			asnrs = getDirectAssigners();
		} catch (ASTException e) {
			throw e;
		} catch (Exception e) {
			if (asnrs == null) throwUnhandledException(e);
		}
		final AssignableProcessor asners = new AssignableProcessor(asnrs);
		final Function ovnFunc = asm.getFunctionScope();
		final int rhsSize = asners.size(); 
		final boolean isGloballyConstAsg = asners == null || asners.isEmpty();
		
		/*	d. else if E� inside elsewhere (including that OV is an array inside dependent loops) :
		 * 		i. PathCond �= versioning OV
		 * 		ii. if OV is global (behind a function call F but NOT by reference), 
		 * 			PathCond �= inserting versions with tag F and index-expansion
		 */
//		final List<IASTNode> ovnBranches = ovNow.getBranchScopes();
//		final boolean isBranchesDependent = ovnBranch instanceof IASTIfStatement 
//				|| ASTUtil.hasAncestorAs(ovnBranch, ovnAsgners.lastOvrBranch, ovnBranches);
//		ovPcOp = isBranchesDependent ? Operator.Or : Operator.And;
		
		/* Case for-branch:
		 * whBranch[whi]: for (...wh[loop#.0] = wh[Case (In-)Dependent-branches]...) {
		 * 	...		
		 * 	wh[loop#.n] = ... wh[loop#.n-1] ...
		 * 	...
		 * }	
		 */
//		if (ovnBranch instanceof IASTForStatement && !isGloballyConstAsg) 
//			ovnCondAntec.and(()-> Proposition.fromParentBranchCondition(
//					ovnBranches.isEmpty() ? null : ovnBranches.get(0), 
//					ovNow.getTopNode(), 
//					Proposition.fromRecursively(ovnAsgm, this), 
//					this));
		
		log(progress, "2: traversing rhs of " + this);
		final Exception e = asners.forEach((AssignableProcessable) (asner -> {
			/* Case Dependent-branches:				Case Independent-branches:
			 * whBranch[whi-1]/TransUnit: {			whBranch[whi-1]: {
			 * 	...										...
			 * 	wh[whi-1] = ...							wh[whi-1] = ...
			 * 	...										...
			 * 	whBranch[whi]: {					}
			 * 		...								...
			 * 		wh[whi] = ... wh[whi-1] ...		whBranch[whi]: {
			 * 		...									...
			 * 	}										wh[whi] = ... 
			 * 	...											whBranch[whi-1].cond 
			 * }											? wh[whi-1] 
			 * 												: (whBranch[whi-2].cond 
			 * 													? wh[whi-2] : ...) ...
			 * 											...
			 * 										}
			 */
			/* Case If-(dependent-)branches:
			 * if|whBranch[whi-n]: {
			 * 	...
			 * 	wh[whi-n] = ...
			 * 	...
			 * } else (if)|whBranch[whi-1]: {
			 * 	...
			 * 	wh[whi-1] = ...
			 * 	...
			 * } else (if)|whBranch[whi]: {
			 * 	...
			 * 	wh[whi] = ... 
			 * 	...
			 * } 
			 */
//			if (isBranchesDependent) {
			
			/* whBranch[whi-n-1]/TransUnit: {
			 * ...
			 * wh[whi-n-1] = ...
			 * ...
			 * if|whBranch[whi-n]: {
			 * 	...
			 * 	wh[whi-n] = ... wh[whi-n-1] ...
			 * 	...
			 * } else (if)|whBranch[whi-1]: {
			 * 	...
			 * 	wh[whi-1] = ... wh[whi-n-1] ...
			 * 	...
			 * } else (if)|whBranch[whi]: {
			 * 	...
			 * 	wh[whi] = ... wh[whi-n-1] ...
			 * 	...
			 * } 
			 * 	...
			 * } 
			 */
//				if (ovnAsgner.equalsVariable(ovNow)) throwTodoException(
//						"If-else with wh[whi] = ... wh[whi-n-1] ...");
			
			/* (default assignment) if|whBranch[whi-n]: {
			 * 	...
			 * 	wh[whi-n] = ... rhsv ...
			 * 	...
			 * } else (if)|whBranch[whi-1]: {
			 * 	...
			 * 	wh[whi-1] = ... rhsv ...
			 * 	...
			 * } else (if)|whBranch[whi]: {
			 * 	...
			 * 	wh[whi] = ... rhsv ...
			 * 	...
			 * } 
			 */
//			} 
			
			/* Case Initial-non-for-(non-)branch:
			 * whBranch[0]: {
			 * 	...
			 * 	wh[0] = ... rhsv ...
			 * 	...
			 * }
			 */
//			else if (ovnAsgners.lastOvrBranch == null || ovnBranch == ovnAsgners.lastOvrBranch) {
			
			/* whBranch/TransUnit: {
			 * 	...
			 * 	wh[whi-1] = ...
			 * 	... 
			 * 	wh[whi] = (non CONST.)
			 * 	... 
			 * } 
			 */
//				if (!isGloballyConstAsg) {
//					if (ovnAsgner.equalsVariable(ovNow)) {
			/*	1. for each revised (including rewritable) OV self reference in E :
			 * 	Each assignment after reading (including rewritingly assigned) is a reversion.
			 * 
			 * whBranch/TransUnit: {
			 * 	...
			 * 	wh[whi-1] = ...
			 * 	... 
			 * 	wh[whi] = ... wh[whi-1] ...
			 * 	... 
			 * } 
			 */
//						PathVariable.versionWith(ovNow);
//						if (ovRef.isGlobal()) PathVariable.versionWith(ovRef, ovrFunc);
//						else if (whi_ >= 0) PathVariable.versionWith(ovRef, whi_);
//					}
			
			/*	2. (default self-independent) else for each rhs dependent variable reference DV of OV in 
			 * 	E : PathCond �= getVOPCond(DV, P)
			 * 
			 * whBranch/TransUnit: {
			 * 	...
			 * 	wh[whi-1] = ...
			 * 	... 
			 * 	wh[whi] = ... rhsv ...
			 * 	... 
			 * } 
			 */
//				}
//			}
			
//			else if (whi > 0) {
//				Assignable lastWr = wh[whi - 1];
//				// outer branches
//				if (lastWr.getBranchScopes().isEmpty()) PathVariable.versionWith(
//						ovNow, whi);
//				// other branches
//				else ovNow.reversion(MutexAssignedVersion.from(
//						lastWr, whSet.headSet(wh[whi]), ThreadRole.MASTER));
//			}
			
			final String rhsProgress = progress + "-" + (asners.i + 1) + "/" + rhsSize 
					+ "(" + asner.getShortNameAddress() + ")"; 
			if (asner.selfAssigns()) return true;	// self assignment condition is computed by getPathCondition() already
			
			final VODConditions rhsCond = asner.getConditions(rhsProgress);
			if (rhsCond == null) return false;
//			if (rhsCond.isEmpty()) throwReductionException();
			andSideEffect(()-> rhsCond);
			
			if (!isGloballyConstAsg) 
				if (traverseCallers(asner, ovnFunc, condConsq, rhsProgress) != null)
					return false;
			// traversing callees
//			if (ovNow.isFunctionCall()) {
//				ovNow.andSideEffect(()-> Function.get(ovRef.getName(), , this);
//			}
			
//			ovnAsgners.lastOvrBranch = ovnBranch;
			log(rhsProgress, "finished genCond of rhs " + asner);
			return true;
		}));
		if (e != null) throwTodoException(toString() + " = " + asners, e);	// uncertain rhs
		
		log(progress, "3: updating pathCond of " + this);
//		log(whProgress, "already completed WH of " + ov);
//		if (ovrPcAntec.isEmpty()) Debug.throwReductionException();
		if (!condConsq.isEmpty()) condAntec.imply(condConsq); 
		andSideEffect(()-> condAntec);
		
		return getSideEffect();
	}
	
	/**
	 * 	genVOPCond(OV, P), given an observed variable, OV, and its observation expression line position, P, ::=
	 * 		(pathBeginCond -> pathNextCond)*
	 * 
	 * @param progress
	 * @return All of side-effect, parallel and path condition work on a 
	 * <em>semantically (runtime) assigned</em> assignable (assignment).
	 */
	public VODConditions getConditions(final String progress) 
			throws IncomparableException, ASTException {
		final Boolean isA = isAssigned();
		if (isA == null) throwUncertainException(toString());
		
		VODConditions conds = null;
		// path condition
		if (isA) conds = getAssignmentConditions(progress);
		
		/*	i. finding writing reference holder expressions (writing-history) 
		 * 	of OV, WRS, before P, while conditions need semantically previous 
		 * 	assigned assignable's
		 */
		else try {
			for (VersionEnumerable<PV> pra : previousRuntimeAssigneds()) {
				final VODConditions subConds = guardThrow(()-> getThrow(
								()-> ((Assignable<PV>) pra).getConditions(progress),
								()-> log(progress, "no more assignments for " + this)),
								METHOD_GET_CONDITIONS);
				if (subConds != null) {
					if (conds == null) conds = subConds;
					else conds.or(subConds);
				}
			}
			
		} catch (ReenterException e) {	// thrown by recursive getConditions(...)
			throw e;
		} catch (Exception e) {
			throwUnhandledException(e);
		}

		// parallel condition
		if (conds == null) throwTodoException("conditions");
		for (OmpDirective dir : getEnclosingDirectives())
			conds.and(dir.getCondition());
		return conds;
		
//		if (isDone() || isFunction() || enters(METHOD_GET_CONDITIONS)) 
//			return getConditions();	// throwIllegalStateException("uncertain condition");
//		
//		final SortedSet<Assignable> whSet = cg.getWritingHistoryOfBeforeTP(this).headSet(this, true);
//		if (whSet == null || whSet.isEmpty()) {
//			log(null, "No writing history for " + this);
//			return leave(METHOD_GET_CONDITIONS);
//		}
//		final Assignable[] wh = whSet.toArray(new Assignable[]{});	assert wh != null;
//		final int whSize = wh.length;								assert whSize > 0;
//		
//		for (int whi = whSize - 1, whi_ = -1; whi >= 0; whi--) {
//			/* testing at beginning of each iteration for updates 
//			 * completed by following sub-condition generation calls
//			 * and avoiding redundant traversal which is already  
//			 * run by preceding condition generation calls?
//			 */
//			final Assignable ovNow = wh[whi];
//			if (ovNow != this && ovNow.enters(METHOD_GET_CONDITIONS)) continue;
//			try {
//				final String whProgress = (progress == null || progress.isEmpty() ? "" : progress + "-") 
//						+ Integer.valueOf(whi + 1) + "/" + whSize + "[" + ovNow.getShortNameAddress() + "]";
//				final int whi__ = whi;
//				ovNow.enter(METHOD_GET_CONDITIONS);
//				ovNow.setWorkRemaining();
//				ovNow.andSideEffect(()-> ovNow.getConditions(whi__, wh, whSet, whProgress));
//				ovNow.done(whProgress, 
////							"[xsize: antec " + ovrCondAntec.getExtraSize() + ", ref " + ovRef.getExtraSize() + ", ov " + ovPc.getExtraSize() + "]" + 
//							"saved WH of " + ovNow);
//				ovNow.leave(METHOD_GET_CONDITIONS);
//				
////				Operator ovPcOp = Operator.And;
////				switch (ovPcOp) {
////				/* whCond_a && (whCond_b || whCond_c) && whCond_d	=	
////				 * whCond_a && ((whCond_b && whCond_d) || (whCond_c && whCond_d))
////				 */
////				case Or:	orCond.orSideEffect(ovNowCond);	break;
////				// whCond_a <=> whCond_b <=> whCond_c && whCond_c	=	whCond_a && whCond_b && whCond_c
////				case And:
////					if (orCond.hasSideEffect()) {
////						ovPv.andSideEffect(orCond.getSideEffect()); 
////						orCond = new VOPConditions(this);
////					}
////					ovPv.andSideEffect(ovNowCond);	
////					break;
////				case False:
////				case FunctionCall:
////				case Iff:
////				case Imply:
////				case Not:
////				case True:
////				case Xor:
////				default:	throwTodoException("unsupported operation"); break;
////				}
////				if (pathNextCond.isEmpty()) cond.implyLater(pathBeginCond);	// ex. TODO
////				else cond.andImplyIn(pathCond, Function.getBooleanOne(		// ex. TODO
////						ASTUtil.getEnclosingFunctionCallNameOf(ovRef.getTopNode())));
////				if (!ovrd.getSideEffect().toString().contains(ovrd.getName().toString())) 
////					throwReductionException();
//				
//			} catch (IllegalStateException | IncomparableException | ASTException e) {
//				ovNow.leave(METHOD_GET_CONDITIONS);
//				if (whi_ == whi) throw e;
//				whi_ = whi;
//				whi = whSize;
//			} catch (Exception e) {
//				throwUnhandledException(e);
//			}
//		}
//		
//		// clear the 'or' condition at last in case of no 'and' operations performed
////		if (orCond.hasSideEffect()) ovPv.andSideEffect(orCond.getSideEffect()); 
//		return getConditions();
	}


	
//	private Predicate generatePredicateOfConstLoopFrom(IASTName ov, IASTForStatement loop, IASTExpression exp) {
//	PathVariable.versionConstantlyWith(ov, loop);
//	return new Predicate(
//			PathVariable.get(ASTUtil.getEnclosingCanonicalLoopIteratorOf(ov)), 
//			generateEqualitiesOfConstLoopFrom(ov, loop, exp));
//}

//private Collection<Equality> generateEqualitiesOfConstLoopFrom(
//		IASTName ov, IASTForStatement loop, IASTExpression exp) {
//PathVariable.versionConstantlyWith(ov, loop);
//	return eqs;
//}



	/**
	 * Traversing the rhs caller conditions of lhs assignable.
	 * 
	 * @param rhs - a parameter of <code>callee</code>
	 * @param callee
	 * @param condConsq
	 * @param progress
	 * @return
	 */
	@SuppressWarnings("unchecked")
	private Exception traverseCallers(final Assignable<?> rhs,
			final Function callee, final VODConditions condConsq, final String progress) 
					throws IncomparableException, ASTException {
		int pi = callee.getParameterIndex(rhs);
		if (pi == -1) return null;
		
		final Assignable<?> tv = getCondGen().getTargetVariable();
		final AssignableProcessor preCallers = new AssignableProcessor(new HashSet<>());
		for (FunctionCall<?> fc : rhs.getPreceedingCallers()) 
			for (PathVariablePlaceholder v : 
				fc.getArgument(pi).getDirectPathVariablePlaceholders()) {
				final Assignable<?> caller = v.getAssignable();
				if (tests(caller.isBefore(tv))) preCallers.add((Assignable<PV>) caller);
			}
		
		if (preCallers.isEmpty()) return tv.throwIncomparableException(
				rhs, "No such path for: " + rhs);
		
		return preCallers.forEach((AssignableProcessable) caller -> {
			log(progress, "genCond caller " + caller);
			VODConditions callerCond = caller.getConditions(progress);
//				callerCond.getPathCondition().replaceByCall(firstCall_);
			condConsq.and(callerCond);
			return callerCond != null;
		});
		
		/*	3. else if E� behind a void function call F TODO: or pointer P by reference : 
		 * 	building a corresponding SMT function TODO: or a pointer chain
		 */
	}
	
	
	
	public VODConditions getSideEffect() {
		try {
			return getPathVariablePlaceholder().getSideEffect();
			
		} catch (UncertainPlaceholderException e) {
			throw e;
		} catch (Exception e) {
			return throwTodoException(e);
		}
	}
	
	/**
	 * Adding indirect side effect (to the path variable delegate) as a conjunction.
	 * @param newSideEffect
	 */
	public void andSideEffect(
			Supplier<? extends SideEffectElement> newSideEffect) {
		// same-level side-effect 'and'
		getPathVariablePlaceholder().andSideEffect(newSideEffect);
	}
	
	/**
	 * Adding indirect side effect (to the path variable delegate) as a disjunction.
	 * @param newSideEffect
	 */
	public void orSideEffect(Supplier<? extends SideEffectElement> newSideEffect) {
		// same-level side-effect 'or'
		getPathVariablePlaceholder().orSideEffect(newSideEffect);
	}
	
//	public int getExtraSize() {
//		return toString().length() + Elemental.getAltNull(
//				()-> getPathVariableDelegate().getSideEffect().toString().length(), 0);
//	}

	public IASTFileLocation getFileLocation() {
		return nameView != null ? nameView.getFileLocation() : null;
	}

	@Override
	public IASTNode getASTAddress() {
		return getASTName();
	}
	
	/* (non-Javadoc)
	 * @see ompca.vodcg.Addressable#getShortAddress()
	 */
	@Override
	public String getShortAddress() {
		final IASTFileLocation loc = getFileLocation();
		if (loc == null) return get(()-> cacheRuntimeAddress().getShortAddress(),
				()-> throwNullArgumentException("dynamic address"));
		try {
			final int sl = Elemental.getNonNull(()-> loc.getStartingLineNumber());
			final Assignable<PV> p = previous(true), n = next(true);
			if ((p != null && p.getFileLocation().getStartingLineNumber() == sl) ||
					(n != null && n.getFileLocation().getStartingLineNumber() == sl))
				return ASTUtil.toLineOffsetLocationOf(loc);
		} catch (IncomparableException e) {
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
		return ASTUtil.toLineLocationOf(loc);
	}
	
	public String getShortNameAddress() {
		return getName() + "_" + getShortAddress();
	}
	
	public IASTNode getTopNode() {
		if (expView != null) return expView; 
		if (nameOwnerView != null) return (IASTNode) nameOwnerView;
		return throwTodoException("null top node");
	}

	public IASTInitializerClause getParentClause() {
		final IASTNode top = getTopNode();
		return top instanceof IASTInitializerClause
				? (IASTInitializerClause) top
				: ASTUtil.getAncestorClauseOf(top, false);
	}
	
	/**
	 * Return the first initializer-clause child of either expression statement or declarator 
	 * where the named ID occurred in.
	 *  
	 * @return
	 */
	public IASTInitializerClause getFirstClause() {
		if (nameOwnerView instanceof IASTDeclarator) {
			IASTInitializer init = ((IASTDeclarator) nameOwnerView).getInitializer();
			if (init instanceof IASTEqualsInitializer) {
				isAssigned = true;
				return ((IASTEqualsInitializer) init).getInitializerClause();
			} else if (init != null)
				return throwTodoException("Unsupported initializer!");
		}
		
		return getParentClause();
	}

	/**
	 * An assignment includes both assigning or assigned Lv's.
	 * 
	 * @return The direct assignment as an (equals) initializer in a declarator 
	 * 	({@link IASTEqualsInitializer}) or initializer clause in more complex expression
	 * 	({@link IASTInitializerClause}).
	 */
	public Assignment getFirstAssignment() {
		if (firstAssignmentView != null) return firstAssignmentView;
		
		IASTInitializerClause clause = getFirstClause();
		while (clause != null) try {
			final IASTNode cp = clause.getParent();
			if (cp instanceof IASTEqualsInitializer) 
				firstAssignmentView = Assignment.from((IASTEqualsInitializer) cp, cacheRuntimeAddress(), getCondGen());
			else if (clause instanceof IASTFunctionCallExpression 
					&& isCallByReference()) {
				// declared array - isArray() && isPointer()
				firstAssignmentView = Assignment.from((IASTFunctionCallExpression) clause, this, getCondGen());
				break;
			} else
				// dereferenced array - !isArray() && isPointer()
				firstAssignmentView = Assignment.from(clause, this, getCondGen());				
//			else if (isAssigned) 
//				throwTodoException("unsupported assignment type?");
			
			if (firstAssignmentView != null) break;
			
			// traversing ancestor
			clause = ASTUtil.getAncestorClauseOf(clause, false);
//			if (ASTLValueComputer.isAssigningOf(clause, nameView)
//					|| ASTLValueComputer.isAssignedTo(clause, expView)) break;
			
		} catch (Exception e) {
			throwTodoException(e);
		}
		setAssigned(firstAssignmentView); 
		return firstAssignmentView;
	}

	
	
	/**
	 * @return @NotNull
	 */
	public Set<Assignable<?>> getArguments() {
//		if (isArrayArgument() || isCallArgument()) return Collections.singleton(this);
		return getArrayArguments();
	}
	
	/**
	 * @return @NotNull
	 */
	public Set<Assignable<?>> getArrayArguments() {
		if (isArray()) {
			final Set<Assignable<?>> args = new HashSet<>();
			final ASTAddressable rt = getRuntimeAddress();
			final VODCondGen cg = getCondGen();
			if (isDeclarator()) args.addAll(fromOf(getDeclarator(), rt, cg));
			else for (IASTArraySubscriptExpression asub : getEnclosingArraySubscriptExpressions())
				args.addAll(fromOf(asub.getSubscriptExpression(), rt, cg));
//			for (ArithmeticExpression arg : getNonNull(()-> 
//			getEnclosingArray().getArguments()))
//				for (PathVariablePlaceholder pvp : 
//					((Expression) arg).getDirectPathVariablePlaceholders())
//					args.add(pvp.getAssignable());
			return args;
		}
		return Collections.emptySet();
	}
	
	/**
	 * @return a neither null nor duplicated argument list.
	 * 	The arguments are for some functional version.
	 */
	public List<ArithmeticExpression> getFunctionalArguments() 
			throws ASTException, IncomparableException, 
			UncertainPlaceholderException, NoSuchVersionException {
		// guaranteeing non-duplicated loop iterators
		final List<ArithmeticExpression> args = new ArrayList<>();
		final Set<IASTStatement> loops = new HashSet<>();
		
		// array arguments first
//		final ArrayPointer ea = getEnclosingArray();
//		if (ea != null) {
//			args.addAll(ea.getArguments());
//			for (ArithmeticExpression arg : args) {
//				if (arg instanceof ConditionElement)
//					for (PathVariablePlaceholder argp : ((ConditionElement) arg).getDirectPathVariablePlaceholders()) 
//						if (argp.isLoopIterator()) 
//							loops.add(argp.getAssignable().getIteratingCanonicalLoop());
//			}
//		}

		// loop arguments then
		for (Assignable<?> asg : getAssigners()) 
			if (asg.isLoopIteratingIterator()) 
				if (loops.add(asg.getIteratingCanonicalLoop())) 
					args.add(asg.getPathVariablePlaceholder());
		
		return args;
	}
	
	
	
	/**
	 * @return @NotNull the assigned of the same variable.
	 * 	For inside loop assignable's: multiple assigned's consisting of 
	 * 	the previous assigned followed by the next assigned;
	 * 	For outside loop ones: previous assigned.
	 */
	@SuppressWarnings("unchecked")
	public <T extends Assignable<PV>> NavigableSet<T> getAssigneds() {
		if (tests(isAssigned())) {
			final NavigableSet<T> singleton = new TreeSet<>(this);
			singleton.add((T) this);
			return singleton;
		}
		return previousRuntimeAssigneds();
		
//		if (debugTests(()-> isAssigned())) try {
//			return MutexAssignedVersion.from((Assignable<PathVariable>) this).getAssigneds();
//			
//		} catch (NoSuchVersionException e) {
//			return Collections.singleton(this);
//			
//		} catch (Exception e) {
//			throwTodoException(e);
//		}
//		
//		final Set<Assignable<?>> asds = new HashSet<>();
//		final Assignable<PV> pAsd = previousAssigned();
////		final Assignable pAsd = previousRuntimeAssigned();
//		if (pAsd != null && !hasMutexBranchTo(pAsd)) asds.add(pAsd);
//		
//		final Assignable<PV> nAsd = nextLocallyAssigned();
//		if (nAsd != null && selfAssigns()) asds.add(nAsd);
////		if (nAsd != null && !hasMutexBranchTo(nAsd) 
////				&& hasSameIterationAs(nAsd)) asds.add(nAsd);
//		
//		return asds;
	}
	
	/**
	 * @return @NotNull assigned's even for their non-assigned neighbors.
	 */
	public NavigableSet<Assignable<PV>> getMutexAssigneds() 
			throws ASTException, IncomparableException, UncertainPlaceholderException {
		final NavigableSet<Assignable<PV>> mas = new TreeSet<>(this);
		if (tests(isAssigned())) mas.add(this);
		
		final Set<Assignable<PV>> count1s = new HashSet<>(), 
				count2s = new HashSet<>();
		count1s.add(this); count2s.add(this);
//		mas.addAll(getWritingHistoryOf(getEnclosingIf()));	// maybe inner-most if

		Assignable<PV> asn = this, asd = this;
		boolean findsPre = true;
		while (true) {
			while (true) {
				asd = findsPre 
						? asn.previousAssigned() 
						: asn.nextLocallyAssigned();
				
				/** <pre>
				 * Case (cond ? x : y) ::= z				= (cond && x = z) || (!cond && y = z) 
				 * Case (cond ? true/false : y) ::= z		=> uncertain x (current assigned)		=> never happens
				 * Case (cond ? x : true/false) ::= z		=> uncertain y (next assigned)
				 * </pre>
				 */
//				if (asd == null) throwNoSuchVersionException("No next assigned");
				if (asd == null) {
					if (!findsPre) return mas;
					findsPre = !findsPre;
				} else {
					asn = asd;
					if (count1s.add(asd)) break;
					else if (count2s.size() == count1s.size()) return mas;
					else count2s.add(asd);
				}
			}
			
			// hasMutexBranchAs -> getMutexBranchCondition -> mas
			final IASTStatement mb = getMutexBranchTo(asd);
			if (mb != null) try {
				// for if-else condition: cond = F => the following if-else sub-conditions are unreachable
				if (!Proposition.fromParentBranchCondition(
						mb, asd.getTopNode(), null, getCondGen()).isFalse()) 
					mas.add(asd);
			} catch (Exception e) {
				throwTodoException(e);
			}
		} 
	}
	
//	@Override
	@SuppressWarnings("unchecked")
	public Expression getAssigner() throws ASTException {
		final Set<Assignable<PV>> asds = getAssigneds();
		final int size = asds.size();
		if (size == 0) return null;
		
		// Expression.fromRecursively() returns the assigned
		// or size == 2 -> loop iterator in the iterating condition
		if (size == 1 || isLoopIteratingIterator()) 
			return getSkipNull(()-> asds.iterator().next().getDirectAssigner().get(0));
		
		// mutex-assigned or functional version assigner for multiple assigned's
		if (isMutexAssigned()) for (Assignable<?> asd : asds) {
			if (asd == this) return getDirectAssigner().get(0);
		} else for (Assignable<?> asd : asds) try {
			return FunctionalVersion.from((Assignable<PathVariable>) asd).getAssigner();
			
		} catch (NoSuchVersionException e) {
			continue;
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
		return throwTodoException("unsupported multiple assigneds");
	}
	
	/**
	 * @return non-null
	 * @throws ASTException
	 * @throws UncertainException
	 */
	@SuppressWarnings("unchecked")
	public Set<Assignable<?>> getAssigners() 
			throws ASTException, UncertainException {
		if (tests(isConstant())) return getDirectAssigners();
		
		if (isDirty() || assigners.isEmpty()) {
			final Boolean isA = isAssigned();
			if (isA == null) throwUncertainPlaceholderException();
			if (isA) {
				assert ASTUtil.hasAncestorAs(nameView, getFirstAssignment().toASTNode(), null);
				for (Assignable<?> asnr : getDirectAssigners()) addAssigner(asnr);
				
				// traversing parent condition including parent conditions for side-effect assigners
				try {
					debugRun(()-> consumeSkipNull(
							vps -> {for (PathVariablePlaceholder vp : vps) {
								final Assignable<?> asnr = vp.getAssignable();
								if (asnr != null && asnr != this) addAssigner(asnr);
							}}, 
							()-> getPathCondition().getDirectPathVariablePlaceholders()));
				} catch (ASTException | UncertainException e) {
					throw e;
				} catch (Exception e) {
					throwUnhandledException(e);
				}
				
			} else runSkipNull(()-> {
				for (Assignable<?> asd : getAssigneds()) 
					for (Assignable<?> asnr : asd.getAssigners()) 
						addAssigner(asnr);	
			});
			
			setNotDirty();
		}
		return Collections.unmodifiableSet(assigners);
	}
	
//	/**
//	 * Assigners are all right-hand-side variable references used by the l-value's 
//	 * path (including parent) condition.
//	 * Assigners always belong to {@link IASTExpression}'s since they're r-values.
//	 * 
//	 * @param sideEffect - conditional or expression-al side-effect store if needed
//	 * @return Non-null direct or indirect (side-effect) assigners
//	 */
//	public Set<Assignable> getAssigners(VODConditions sideEffect) 
//			throws UncertainException, ASTException {
//		if (sideEffect != null) try {Elemental.consumeAltEmpty(
//				se-> sideEffect.and(se), 
//				()-> getConditions(null), 
//				()-> log(this + " has no side-effect."));
//		
//		} catch (ASTException e) {
//			throw e;
//		} catch (Exception e) {
//			throwUnhandledException(e);
//		}
//		return getAssigners();
//	}

	public List<Expression> getDirectAssigner() {
		return debugGetSkipNull(()->
		getFirstAssignment().getAssigners());
	}
	
	/**
	 * @return @NotNull
	 * @throws ASTException
	 * @throws UncertainException
	 */
	public Set<Assignable<?>> getDirectAssigners() 
			throws ASTException, UncertainException {
		try {
			if (tests(isAssigned())) 
				return addAssigners(getFirstAssignment().getAssignerAssignables()); 
			
//			final Set<Assignable<?>> das = new HashSet<>();
//			for (Assignable<?> asd : getAssigneds())
//				das.addAll(asd.getDirectAssigners());
//			return addAssigners(das);
			
		} catch (NullPointerException e) {
			assert getFirstAssignment() == null;

		} catch (ASTException | UncertainException e) {
			throw e;
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
		return Collections.emptySet();
	}
	
	private boolean addAssigner(Assignable<?> asgnr) {
		assert asgnr != null;
		asgnr.monitor = splitMonitor();
		return assigners.add(asgnr);
	}
	
	private Set<Assignable<?>> addAssigners(Set<Assignable<?>> asns) {
		assert asns != null;
		for (Assignable<?> asn : asns) addAssigner(asn);
		return asns;
	}
	
	
	
	/**
	 * @param asm - always a direct assignment
	 * @return
	 */
	@SuppressWarnings("unchecked")
	private Boolean setAssigned(Assignment asm) {
		if (asm == null) 
			isAssigned = isParameter();
//		else if (isArgument()) 
//			isAssigned = asm.getAssigned() == this;
		else if (isCallByReference()) try {
			if (asm.isFunctionCall()) isAssigned = trySkipNullException(
					new Class[] {ASTException.class, ReenterException.class},
					()-> getEnclosingCallParameter().isAssigned(),
					()-> asm.getCallAssigner().getParameter(this).isAssigned(),
					()-> ((AssignableExpression) getEnclosingCallArgument()).isAssigned(),
					()-> ((AssignableExpression) getEnclosingCallArgument()).isLikelyAssigned()
					);
			else 
				isAssigned = true;	//equalsVariable(asm.getAssigned());
//				throwTodoException("unsupported function call argument");
		} catch (Exception e) {
			throwTodoException(e);
		}
		else 
			isAssigned = asm.isDirectlyAssignedTo(nameView);
		return isAssigned;
	}
	
	/**
	 * A function assignable represents a functional relation instance,
	 * therefore an assignment more than an assigned.
	 */
	@Override
	public Boolean isAssigned() {
		if (isAssigned != null) return isAssigned;
		if (isASTFunction()) return isAssigned = false;
		
		return guard(
				()-> setAssigned(getFirstAssignment()), 	// may change isAssigned
				()-> null,
				METHOD_IS_ASSIGNED);
	}
	
	public boolean isLikelyAssigned() {
		if (tests(isAssigned) || isArray()) return true;
		
		IASTInitializerClause clause = getFirstClause();
		// traversing ancestor
		while (clause != null) {
			if (ASTAssignableComputer.isLikeAssignment(clause)) return true;
			clause = ASTUtil.getAncestorClauseOf(clause, false);
		}
		return false;
	}
	
	public boolean isSelfAssigned() {
		if (!tests(isAssigned())) return false;
		
		final Set<Assignable<?>> das = getDirectAssigners();
		if (das.isEmpty()) return false;							// empty assigners -> constantly/not assigned
		if (das.contains(this)) return true;
		for (Assignable<?> da : das) if (equals(da)) return true;	// non-abbreviated self assigned
		return false;
	}
	
	public boolean isMutexAssigned() {
		final Assignable<PV> pAsn = previous(true), nAsn = next(true);
		return tests(isAssigned())
				&& ((pAsn != null && hasMutexBranchTo(pAsn))
				|| (nAsn != null && hasMutexBranchTo(nAsn)));
	}
	
//	/**
//	 * @param exp
//	 * @return true <em>only if</em> this assignable is a call-by-reference argument, i.e., 
//	 * possibly assigned during (<em>not</em> after) the given function call
//	 */
//	public boolean isAssignment(IASTFunctionCallExpression exp) {
//		if (exp == null) throwNullArgumentException("function call expression");
//		
//		// call-by-reference = !call-by-value
//		if (!isCallArgument()) return false;
//		if (getType().isPrimitive() && isDereference()) return false;
//		
//		// TODO: precise assigned-checking using simple delegates with delegate versions to avoid circular dependency
////		final VOPCondGen cg = getCondGen();
////		final FunctionCall<?> call = FunctionCall.fromRecursively(exp, null, cg);
////		final Function f = call.getCallee();
////		if (f.isInLibrary()) return false;	// library functions are argument-immutable for now	
////
////		try {
////			final PathVariable p = (PathVariable) f.getParameter(call.getArgumentIndex(this));
////			// parameter.getASTName() == null
////			for (Assignable pAsn : fromOf(ASTUtil.getWritingFunctionDefinitionOf(f.getASTName()), p.getName(), cg)) {
////				final Boolean pia = pAsn.isAssigned();
////				if (pia == null) throwUncertainDelegateException();
////				if (pia) return true;
////			}
////		} catch (IndexOutOfBoundsException | ClassCastException e) {
////			throwTodoException("not a containing assignment");
////		}
////		return false;
//	}
	
//	public boolean isAssigning() {
//		if (isAssigning != null) return isAssigning;
//		
//		Assignment fa = getFirstAssignment();
//		if (fa == null) isAssigning = true;
//		else isAssigning = isAssigned() ? fa.isUnary() : true;
//		return isAssigning;
//	}
	
	/**
	 * @param lhs
	 * @return true if this assignable directly assigns {@code lhs}. 
	 */
	public boolean isDirectlyAssigningTo(Assignable<?> lhs) 
			throws ASTException {
		if (lhs == null || testsNot(lhs.isAssigned)) return false;
		
		final Assignment asm = lhs.getFirstAssignment();
		if (asm == null) return false;
		
		if (asm.isUnary() && lhs == this) return true;
		
		if (asm.isBinary()) 
			if (asm.getAssigned() == lhs) {
				final ASTAddressable da = cacheRuntimeAddress();
				// lhs != null and no exceptions
				for (IASTName rhs : ASTUtil.getDescendantsOfAs(
						asm.getAssignerClause(), IASTName.class)) try {
							if (this == from(rhs, da, getCondGen())) return true;
						} catch (ASTException e) {
							continue;	// rhs has exception => rhs != lhs
						}
			}
		
		return false;
	}

	public boolean isUnsigned() throws IncomparableException {
		final IASTDeclarator decl = getDeclarator();
		if (decl == null) {
			final Assignable<PV> pre = previous();
			return pre != null && pre.isUnsigned();
		}
		
		@SuppressWarnings("unchecked")
		final IASTSimpleDeclaration sd = (IASTSimpleDeclaration) ASTUtil.getAncestorOfAs(
				nameView, new Class[] {IASTSimpleDeclaration.class}, false);	
		if (sd == null) return false;	// throwTodoException("unsupported declaration");
		
		final IASTDeclSpecifier ds = sd.getDeclSpecifier();
		return ds instanceof IASTSimpleDeclSpecifier
				&& ((IASTSimpleDeclSpecifier) ds).isUnsigned();
	}

	/**
	 * @return true <em>only if</em> in the pattern of self-assigning variable x = x op ... or 
	 * 	self-assigning array x[i] = x[j] op ...
	 */
	public boolean selfAssigns() {
		if (isASTFunction()) return false;
		return get(()-> getFirstAssignment().selfAssigns(),
				()-> false);
//		if (isArray()) throwTodoException("self-assigning array");

//		try {
//		Assignable<PV> asd = null, asnr = null;
//		if (tests(isAssigned())) {
//			
//			asd = this;
//			asnr = next();
//			
//		} else {
//			if (!isArray()) return get(()-> getExpressionView().isLValue(),
//					()-> false);
//			
//			// isLValue() for array assignable's checks no indices
//			asd = nextLocallyAssigned();
//			asnr = this;
//		}
//		return asd != null && asnr != null && asnr.equals(asd);
////		return asd != null && asnr != null && asnr.isDirectlyAssigningTo(asd);
//		
//		} catch (Exception e) {
//			return throwTodoException(e);
//		}
		
//		return isCallArgument() && isLikelyAssigned() 
//				? Elemental.tests(getEnclosingFunctionCall().getParameter(this).isAssigned())
//				: Elemental.getAltNull(
//						()-> isDirectlyAssigningTo(getFirstAssignment().getAssigned()), ()-> false);
	}

//	public boolean isCompletingGenCond(Method methodGenCond) {
//		return completesGenCond || enters(methodGenCond);
//	}
//
//	public void completeGenCond(Method methodGenCond) {
//		if (methodGenCond != null) leave(methodGenCond);
//		completesGenCond = true;
//	}
	

	
	public boolean hasArguments() {
		return !getArguments().isEmpty();
	}
	
	public boolean hasSameIterationAs(final Assignable<?> asn2) {
		final IASTStatement loop = getSameLoopOf(asn2);
		return loop != null && hasSameIterationAsOf(asn2, loop);
	}
	
	public boolean hasSameIterationAsOf(Assignable<?> asn2, IASTStatement branch) {
		if (asn2 == null) throwNullArgumentException("assignable");
		return ASTUtil.isSameIterationOf(nameView, asn2.nameView, branch);
	}
	
	public boolean hasSameBranchAsOf(Assignable<?> asn2, IASTStatement branch) {
		if (asn2 == null) throwNullArgumentException("assignable");
		return ASTUtil.isSameBranchOf(nameView, asn2.nameView, branch);
	}
	
	public boolean hasMutexBranch() {
		if (getEnclosingIf() == null) return false;
		
		final Assignable<PV> pasn = previous(true),
				nasn = next(true);
		return (pasn != null && hasMutexBranchTo(pasn)) 
						|| (nasn != null && hasMutexBranchTo(nasn)); 
	}

	/**
	 * The AST Then-clause and Else-clause share the same If-branch scope 
	 * but mutual-exclusive conditions.
	 * 
	 * @param asn2
	 * @return
	 */
	public boolean hasMutexBranchTo(final Assignable<?> asn2) {
		return getMutexBranchTo(asn2) != null;
	}
	
	public IASTStatement getMutexBranchTo(final Assignable<?> asn2) {
		if (asn2 == null) throwNullArgumentException("assignable");
		
		// if-else statement mutex
		for (IASTStatement bs1 : getBranchScopes()) {
			if (bs1 instanceof IASTIfStatement && ASTUtil.isMutexBranchOf(
					nameView, asn2.nameView, (IASTIfStatement) bs1)) 
				return bs1;
			for (IASTStatement bs2 : asn2.getBranchScopes()) 
				if (bs2 instanceof IASTIfStatement && ASTUtil.isMutexBranchOf(
						nameView, asn2.nameView, (IASTIfStatement) bs2)) 
					return bs2;
		}

		// return statement mutex
		final IASTReturnStatement r1 = nextReturnStatement(),
				r2 = asn2.nextReturnStatement();
		if (r1 == r2) return null;
		final Boolean ib2 = isBefore(asn2);
		if (ib2 == null) return null;
		if (ib2) return r1 != null && !asn2.isBeforeLocally(r1) ? 
				r1 : null;			// asn ... r1 ... asn2 ... r2
		return r2 != null && !asn2.isBeforeLocally(r2) ? 
				r2 : null;			// asn2 ... r2 ... asn ... r1
	}
	
	public boolean hasBranchScopes() {
		return !getBranchScopes().isEmpty();
	}
	
	public IASTStatement getBranchScope() {
		return get(()->
		getBranchScopes().get(0), e-> null);	// IndexOutOfBoundsException
	}
	
	/**
	 * @return non-null branch statement(s), excluding {@link IASTTranslationUnit},
	 * 	which may be empty.
	 */
	public List<IASTStatement> getBranchScopes() {
		if (branches != null) return branches;
		
		branches = new ArrayList<IASTStatement>();
		IASTNode node = getTopNode();
		while (node != null) {
			node = ASTUtil.getParentBranchOf(node);
			if (node != null) branches.add((IASTStatement) node);
		}
		return branches;
	}
	
	public Proposition getBranchCondition() 
			throws ASTException {
		if (branchCond != null) return branchCond;

		// explicit AST branch
		final VODCondGen cg = getCondGen();
		branchCond = Proposition.fromParentBranchCondition(
				getBranchScope(), getTopNode(), null, cg); 
		if (branchCond != null) return branchCond;
		
		// implicit return (control) branch
		final List<IASTReturnStatement> rs = 
				ASTUtil.getReturnStatementsOf(getWritingFunctionDefinition());
		final int rSize = rs.size();
		branchCond = Proposition.PureTrue;	// if (true) return ...
		if (rSize > 1) {
			branchCond = branchCond.not();	// if (false) else-if return ...
			final IASTReturnStatement r = nextReturnStatement();
			for (int i = 0; i <= rSize; i++) {
				final IASTReturnStatement ri = rs.get(i);
				branchCond = branchCond.not().and(()-> 	// else return ...
				Proposition.fromParentBranchCondition(
						ri.getParent(), ri, branchCond, cg));
				if (r == ri) break;
			}
		}
		return branchCond;
	}
	
	
	
	public boolean hasDependingLoop() {
		return !getDependentLoops().isEmpty();
	}
	
	/**
	 * @return non-null
	 */
	@Override
	public List<IASTStatement> getDependentLoops() {
		final List<IASTStatement> loops = new ArrayList<>();
		for (IASTStatement bs :getBranchScopes())
			if (isConditionalTo(bs)) loops.add(bs);
//			if (debugTests(()-> isConditionalTo(bs))) loops.add(bs);
		return loops;
	}
	
	public IASTStatement getSameLoopOf(final Assignable<?> asn2) {
		if (asn2 == null) throwNullArgumentException("assignable");
		
//		for (IASTStatement b : getBranchScopes())
//			if (ASTUtil.isSameConditionOf(nameView, asn2.nameView, b)) return true;
		final List<IASTStatement> bss1 = getBranchScopes(), 
				bss2 = asn2.getBranchScopes();
		for (int i1 = bss1.size() - 1, i2 = bss2.size() - 1; 
				i1 >= 0 && i2 >= 0; i1--, i2--) {
			final IASTStatement bs1 = bss1.get(i1), bs2 = bss2.get(i2);
			if (bs1 != bs2) break;
			if (ASTLoopUtil.isLoop(bs1)) return bs1;	// bs1 == bs2
		}
		return null;
	}
	

	
	public Pointer getEnclosingPointer() {
		IASTInitializerClause parent = getParentClause();
		final ASTAddressable da = cacheRuntimeAddress();
		while (parent != null) {
			final Expression e = Expression.fromRecursively(parent, da, getCondGen());
			if (e instanceof Pointer) return (Pointer) e;
			else if (e instanceof PathVariablePlaceholder) return Pointer.from((PathVariablePlaceholder) e);
			parent = ASTUtil.getAncestorClauseOf(parent, false);
		}
		return null;
	}
	
	public Pointer getEnclosingArray() {
		return ArrayPointer.fromEnclosing(this);
	}
	
	public IASTArraySubscriptExpression getEnclosingArraySubscriptExpression() {
		final List<IASTArraySubscriptExpression> arrays = getEnclosingArraySubscriptExpressions();
		return arrays.isEmpty() 
				? null
				: arrays.get(arrays.size() - 1);
	}
	
	public List<IASTArraySubscriptExpression> getEnclosingArraySubscriptExpressions() {
		return ASTUtil.getEnclosingArraySubscriptsOf(getTopNode());
	}
	
	public FunctionCall<?> getEnclosingCall() 
			throws ASTException, UncertainPlaceholderException {
		try {
			return applySkipNull(
					exp-> FunctionCall.fromRecursively(
							exp, (Supplier<Proposition>) null, getRuntimeAddress(), getCondGen()),
					()-> getEnclosingCallExpression());
			
		} catch (ASTException | UncertainPlaceholderException e) {
			throw e;
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	
	public Expression getEnclosingCallArgument() {
		for (IASTInitializerClause arg : 
			getEnclosingCallExpression().getArguments())	// never null
			if (arg.contains(nameView)) 
				return Expression.fromRecursively(arg, getRuntimeAddress(), getCondGen());
		return null;
	}
	
	public int getEnclosingCallArgumentIndex() {
		int i = 0;
		for (IASTInitializerClause arg : 
			getEnclosingCallExpression().getArguments()) {	// never null
			if (arg.contains(nameView)) return i;
			else i++;
		}
		return -1;
	}
	
	public IASTFunctionCallExpression getEnclosingCallExpression() {
		return ASTUtil.getEnclosingFunctionCallOf(getExpressionView());
	}
	
	/**
	 * @return
	 * @throws ASTException - when there're ambiguous AST function definitions
	 */
	public VariablePlaceholder<?> getEnclosingCallParameter() 
			throws ASTException {
		final int argIdx = getEnclosingCallArgumentIndex();
		return argIdx == -1
				? null
				// getEnclosingCallExpression() != null for ALL functional assignable's
				: Function.from(getEnclosingCallExpression(), cacheRuntimeAddress(), getCondGen())
				.getParameter(argIdx);
	}
	
	
	
	/**
	 * @return non-null directive set sorted in the AST order, but not the enclosing order
	 */
//	@Override
	public NavigableSet<OmpDirective> getEnclosingDirectives() {
		// TODO: caching directives
		NavigableSet<OmpDirective> dirs = null;
		final List<IASTStatement> ess = new ArrayList<>(getBranchScopes());
		if (ess.isEmpty()) ess.addAll(getEnclosingStatements());
		for (IASTStatement es : ess) {
			final NavigableSet<OmpDirective> esDirs = OmpDirective.from(es, getCondGen());
			if (esDirs == null || esDirs.isEmpty()) continue;
			
			if (dirs == null) dirs = esDirs;
			else dirs.addAll(esDirs);
		}
		if (dirs == null) return Collections.emptyNavigableSet();
		
		// caching side-effect
		for (OmpDirective dir : dirs) 
			andSideEffect(()-> dir.getCondition());
		return dirs;
	}
	
	public IASTIfStatement getEnclosingIf() {
		for (IASTStatement bs : getBranchScopes())
			if (bs instanceof IASTIfStatement) 
				return (IASTIfStatement) bs;
		return null;
	}
	
	public IASTWhileStatement getEnclosingWhile() {
		for (IASTStatement bs : getBranchScopes())
			if (bs instanceof IASTWhileStatement) 
				return (IASTWhileStatement) bs;
		return null;
	}
	
	public List<IASTStatement> getEnclosingStatements() {
		final List<IASTNode> ans = ASTUtil.getAncestorsOfUntil(
				getTopNode(), ASTUtil.AST_FUNCTION_DEFINITION);
		if (ans == null) return null;
		
		final List<IASTStatement> ess = new ArrayList<>();
		for (IASTNode an : ans) 
			if (an instanceof IASTStatement) ess.add((IASTStatement) an);
		return ess; 
	}
	
	/**<pre>
	 * Retrieving the direct parent loop within the same function definition.
	 * 
	 * Only supporting the OpenMP canonical for-loop 
	 * ({@linkplain OpenMP http://www.openmp.org/mp-documents/openmp-4.5.pdf}).
	 * 
	 * TODO: getEnclosingLoopCondition(...) for handling break/continue statements and while-loop conditions.
	 * <br>
	 * 
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public IASTForStatement getEnclosingCanonicalLoop() {
		return (IASTForStatement) ASTUtil.getAncestorOfAsUnless(
				getTopNode(), 
				new Class[] {IASTForStatement.class},
				ASTUtil.AST_FUNCTION_DEFINITION, 
				false);
	}

	public Assignable<?> getEnclosingCanonicalLoopIterator() {
		return fromCanonicalIteratorOf(getEnclosingCanonicalLoop(), cacheRuntimeAddress(), getCondGen());
	}

	public Assignable<?> getEnclosingCanonicalLoopInitializedIterator() {
		return fromCanonicalInitializedIteratorOf(getEnclosingCanonicalLoop(), cacheRuntimeAddress(), getCondGen());
	}
	
	public IASTForStatement getIteratingCanonicalLoop() {
		if (!isLoopIterator()) return null;

		IASTForStatement loop = getEnclosingCanonicalLoop();
		Assignable<?> it = getEnclosingCanonicalLoopIterator();
		final ASTAddressable da = cacheRuntimeAddress();
		while (loop != null && !equalsVariable(it)) {
			if ((loop = ASTLoopUtil.getEnclosingLoopOf(loop)) == null) break;
			it = fromCanonicalIteratorOf(loop, da, getCondGen());
		}
		return loop;
	}
	
	/**
	 * @return self-inclusive, if assigned, early writing history
	 */
	public NavigableSet<Assignable<?>> getWritingHistoryBefore() {
		try {
			return getSkipNull(()-> 
			getCondGen().getWritingHistoryOfBeforeTP(this).headSet(this, true));
			
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}

	@SuppressWarnings("unchecked")
	public NavigableSet<Assignable<PV>> getWritingHistoryOf(final IASTIfStatement ifStat) {
		if (ifStat == null) throwNullArgumentException("if statment");
		
		final NavigableSet<Assignable<PV>> wh = new TreeSet<>(this);
		for (Assignable<?> asn : getCondGen().getWritingHistoryOfBeforeTP(this))
			if (ifStat.contains(asn.getTopNode())) wh.add((Assignable<PV>) asn);
		return wh;
	}
	
	public IASTFunctionDefinition getWritingFunctionDefinition() {
		return ASTUtil.getWritingFunctionDefinitionOf(nameView);
	}

	/**
	 * @return
	 */
	public Set<FunctionCall<?>> getPreceedingCallers() {
		IASTName fName = ASTUtil.getNameOf(getWritingFunctionDefinition());
		if (fName == null) return Collections.emptySet();
		
		final VODCondGen cg = getCondGen();
		final ASTAddressable rtAddr = cacheRuntimeAddress();
		final Set<FunctionCall<?>> callers = new HashSet<>();
		for (VariableOrientedDag callerPath : VariableOrientedDag.from(this, cg).getTails()) try {
			if (callerPath == null) continue;
			callers.add(FunctionCall.fromRecursively(
					ASTUtil.getAncestorOfAsUnless(callerPath.getCallee().getTopNode(), 
							ASTUtil.AST_FUNCTION_CALL_EXPRESSION, ASTUtil.AST_STATEMENT_TYPE, false), 
					(Supplier<Proposition>) null, rtAddr, cg));
		} catch (ASTException e) {
			continue;
		}
//		IIndex projIndex = ASTUtil.getIndex(false);
//		try {
//			projIndex.acquireReadLock();
//
//			for (IName fRef 
//					: projIndex.findReferences(fName.resolveBinding())) {
//				IASTName fRefName = ASTUtil.toASTName(fRef);
//				@SuppressWarnings("unchecked")
//				IASTNode fCall = ASTUtil.getAncestorOfAsUnless(fRefName, ASTUtil.AST_FUNCTION_CALL_EXPRESSION,
//						new Class[]{IASTStatement.class}, 
//						false);
//				if (fCall != null && Assignable.from(fRefName, CondGen).isBefore(this)) 
//					callers.add(FunctionCall.fromRecursively(
//						(IASTFunctionCallExpression) fCall, null, CondGen));
//			}
//		} catch (Exception e) {
//			throwTodoException(e);
//		} finally {
//			projIndex.releaseReadLock();
//		}
		return callers;
	}
	
	@Override
	public IASTStatement getPrivatizingBlock() {
		// direct privatizing block - direct AST search first
		IASTStatement pb = getPathVariablePlaceholder().getPrivatizingBlock();
		if (pb != null) return pb;

		// indirect privatizing block
		if (!hasArguments()) return null;
		
		// for AST array or function assignable's having arguments
//		if (!isDeclarator()) return getDeclared().getPrivatizingBlock();
		for (Assignable<?> dasn : getDirectAssigners()) {
			pb = dasn.getPrivatizingBlock();
			if (pb != null) return pb;
		}
		
		return null;
//		return getPrivatizingBlock(getAssigners());
	}
	
//	private IASTStatement getPrivatizingBlock(Assignable<?> asn) {
//		assert asn != null;
//		return getPrivatizingBlock(Collections.singleton(asn));
//	}
	

	
	protected void setPrevious(Assignable<PV> pasn) {
//		if (equalsAddress(pasn) && !selfAssigns()) throwTodoException("truly self-previous");
		if (equalsString(pasn) && !selfAssigns()) throwTodoException("truly self-previous");
		previous = pasn;
	}
	
	
	
	public SubMonitor setWorkRemaining() {
		assert monitor != null;
		getCondGen().worked(++workLeft);
		return monitor.setWorkRemaining(workLeft);
	}
	
	public SubMonitor setWorkRemaining(int workRemaining) {
		assert monitor != null;
		getCondGen().worked(workRemaining - workLeft);
		if (workRemaining != workLeft) workLeft = workRemaining;
		return monitor.setWorkRemaining(workLeft);
	}

	public SubMonitor setWorkRemaining(int workRemaining, String progress, String action) {
		getCondGen().log(progress, action, monitor);
		return setWorkRemaining(workRemaining);
	}
	
	public SubMonitor splitMonitor() {
		assert monitor != null;
		return monitor.split(1);
	}
	
	public void done(String progress, String action) {
		final VODCondGen cg = getCondGen();
		cg.log(progress, action, monitor);
		if (isDone()) return;
		
		assert monitor != null;
		cg.worked(-workLeft);
		monitor.done();
		workLeft = -1;
	}
	
	public boolean isDone() {
		return workLeft < 0;
	}
	

	
	public boolean isASTExpression() {
		return expView != null;
	}
	
	public boolean isAtomicTo(Assignable<?> asn2) {
		if (asn2 == null) throwNullArgumentException("assignable");
		
		final OmpDirective dir = getEnclosingDirectives().first();
		return dir != null 
				&& dir == asn2.getEnclosingDirectives().first() 
				&& dir.isAtomic();
	}
	
	public boolean isArgument() {
		return isArrayArgument() || isCallArgument();
	}
	
	/**
	 * @return true if and only if this assignable is enclosed by 
	 * 	an array pointer with arguments
	 */
	public boolean isArray() {
		return nameOwnerView instanceof IASTArrayDeclarator 
				|| tests(()-> 
		getEnclosingArraySubscriptExpression()
		.getArrayExpression().contains(nameView));
	}
	
	public boolean isEverLoopIndexedAssignedArray() {
		if (isArray()) {
			if (isLoopIndexedArray() && tests(isAssigned())) return true;
			for (Assignable<PV> asn : getOtherAssignedsEqualsVariable())
				if (asn.isLoopIndexedArray()) return true;
		}
		return false;
	}
	
	public boolean isLoopIndexedArray() {
		if (isArray()) {
			// checking directly indexed first
			final Set<Assignable<?>> args = getArrayArguments();
			final IASTForStatement loop = getEnclosingCanonicalLoop();
			if (loop != null) for (Assignable<?> arg : args)
				if (arg.isIteratorOf(loop)) return true;

			// checking indirectly indexed
			final VODCondGen cg = getCondGen();
			final ASTAddressable ra = getRuntimeAddress();
			final Set<Assignable<?>> its = new HashSet<>();
			for (IASTStatement dloop : getDependentLoops())
				if (dloop instanceof IASTForStatement) its.add(fromCanonicalIteratorOf((IASTForStatement) dloop, ra, cg));
			
			for (Assignable<?> it : its)
				for (Assignable<?> arg : args)
					if (arg.equalsVariable(it)) return true;
		}
		return false;
	}
	
	public boolean isArrayArgument() {
		return tests(()-> 
		getEnclosingArraySubscriptExpression()
		.getArgument().contains(nameView));
	}
	
	public boolean isCallArgument() {
		final IASTNode node = getTopNode();
		final List<IASTNode> ancs = ASTUtil.getAncestorsOfUntil(node, null);
		if (ancs == null) return false;
		
		for (IASTNode anc : ancs) 
			if (anc instanceof IASTFunctionCallExpression) {
				final IASTInitializerClause[] args = 
						((IASTFunctionCallExpression) anc).getArguments();
				if (args == null) return false;
				for (IASTInitializerClause arg : args)
					if (arg.contains(node)) return true;
			}
		return false;
	}
	
	public boolean isCallByReference() {
		if (!isCallArgument()) return false;
		
		// checking if this is a leading and pure pointer
		final Expression ea = getEnclosingCallArgument();
		if (ea == null || !(ea instanceof Pointer) || ea.getType().isPrimitive()) 
			return false;
		
		final Pointer ep = (Pointer) ea;	
		return ep.getBeginningPlaceholder().getAssignable() == this 
				&& !ep.getType().isPrimitive();
	}

	@Override
	public boolean isDeclarator() {
		return nameOwnerView instanceof IASTDeclarator;
	}
	
	public Boolean isDirectlyFunctional() {
		return isFunctional(true);
	}
	
	public boolean hasFunctionalArguments() {
		for (Assignable<?> arg : getArguments()) 
			if (arg.isLoopIterator() 
					&& ASTLoopUtil.isLoopParallel(arg.getEnclosingCanonicalLoop(), getCondGen())) 
				return true;
		return false;
	}
	
	public boolean isASTFunction() {
		return getBinding() instanceof IFunction;
	}
	
	/**
	 * @return true if needs any virtual Function to represent the IVariable binding.
	 */
	public Boolean isFunctional() {
		try {
			return debugTests(()-> testsFirst(
					()-> isDirectlyFunctional(), 
					()-> isFunctional(false)));
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	
	/**
	 * @param isDirectly
	 * @return true if its placeholder's version should be functional
	 */
	private Boolean isFunctional(final boolean isDirectly) {
		// loop initialized iterator is write-once
//		if (isLoopInitializedIterator()) return false;
		// loop-functionally self-assigning (even under non-parallel condition) 
		if (isLoopIterator()) return true;
		// functionally self-assigning (and assigner-less): x = x + y, call(array), etc
		if (isLoopConditional() && (isSelfAssigned() || selfAssigns())) return true;
//		// loop iterating iterator changes its value functionally as a function argument
//		if (isLoopIteratingIterator()) return true;
		if (isEverLoopIterator()) return true;
		
		/*
		 * a loop-indexed and assigned array is functional,
		 * or it will generate n new ArrayAccessVersion's given n loop iterations of assigned-ness
		 */
		if (isEverLoopIndexedAssignedArray()) return true;

		if (isDirectly)
			if (!hasBranchScopes() || tests(isDirectlyConstant())) return false;
//		if (isDirectly && hasFunctionalArguments()) return true;
		
//		if (enters(METHOD_IS_FUNCTIONAL)) return null;
//		enter(METHOD_IS_FUNCTIONAL);
		try {
			Boolean isF = null;
			// checking assigner functionally: e.g. i of a[i], etc
			for (Assignable<?> asgn : isDirectly ? 
					getDirectAssigners() : getAssigners()) {
				isF = asgn.guard(()-> asgn.isFunctional(isDirectly),
						METHOD_IS_FUNCTIONAL);
				if (isF == null) continue;
				if (isF) return true;
//				if (isF) return leave(true, METHOD_IS_FUNCTIONAL);
			}
			
			// checking earlier functionally assigned
			if (!isDirectly && isF == null) for (Assignable<?> asn : getOthersEqualsVariable()) {
				isF = asn.guard(()-> asn.isFunctional(),
						METHOD_IS_FUNCTIONAL);	// !this.isDirectly => asn.isDirectly => !asn.isDirectly
				if (isF == null) continue;
				if (isF) return true;
			}
			
			if (isF != null) return isF;	// !isF
//			if (isF != null) return leave(isF, METHOD_IS_FUNCTIONAL);	// !isF
			
			if (tests(isConstant())) return false;
//			return leave(false, METHOD_IS_FUNCTIONAL);
		} catch (UncertainException e) {	// thrown by non-self-recursive call
			return null;
//			return leave((Boolean) null, METHOD_IS_FUNCTIONAL);
		} catch (Exception e) {
			throwUnhandledException(e, METHOD_IS_FUNCTIONAL);
		}
		return null;
//		return leave((Boolean) null, METHOD_IS_FUNCTIONAL);
	}
	
	
	
//	@Override
//	public boolean isFrozen() {
//		return getTopNode().isFrozen();
//	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean isParameter() {
		return getNameOwner() instanceof IASTDeclarator 
				&& ASTUtil.getAncestorOfAsUnless(getASTName(), 
						new Class[]{IASTParameterDeclaration.class},
						ASTUtil.AST_FUNCTION_DEFINITION, 
						false) != null;
	}
	
	public boolean isPointer() {
		return getType() instanceof PointerType;
	}
	
	public boolean isPointerEnclosing() {
		return isPointer()
				|| getEnclosingPointer() != null;
	}
	
	public boolean isReference() {
		return !getType().isPrimitive()	// PointerType
				|| isLikelyAssigned();
	}
	
	public boolean isRuntimeTraversable() {
		return true;
	}
	
	@Override
	public boolean isThreadPrivate() {
		return isArray()
				? isDirectiveLocal()
				: VersionEnumerable.super.isThreadPrivate();
	}
	
	public boolean isDirectiveLocal() {
		final SortedSet<OmpDirective> dirs = getEnclosingDirectives();
		return !dirs.isEmpty()
				&& dirs.equals(getDeclared().getEnclosingDirectives());
	}
	
	public boolean isLocal() {
		return getWritingFunctionDefinition() == getDeclared().getWritingFunctionDefinition();
	}
	
	/**
	 * Including breakable constant loops, such as 
	 * for(;;)...break; and while (true)...break;
	 * 
	 * @return
	 */
	public boolean isLoopConditional() {
		if (!testsNot(isAssigned()))	// isAssigned or isAssigned == null
			for (IASTStatement bs : getBranchScopes()) 
				if (ASTLoopUtil.isLoop(bs) && isConditionalTo(bs)) return true;
		return false;
	}

	@Override
	public boolean isLoopIteratingIterator() {
		for (IASTStatement bs : getBranchScopes()) 
			if (bs instanceof IASTForStatement 
					&& equalsVariable(fromCanonicalIteratorOf(
							(IASTForStatement) bs, null, getCondGen()))) 
				return true;
		return false;
	}
	
	@Override
	public boolean isLoopInitializedIterator() {
		for (IASTStatement bs : getBranchScopes()) 
			if (bs instanceof IASTForStatement 
					&& equalsToCache(fromCanonicalInitializedIteratorOf(
							(IASTForStatement) bs, cacheRuntimeAddress(), getCondGen()))) 
				return true;
		return false;
	}
	
	public boolean isEverLoopIterator() {
		for (Assignable<PV> asn : getOthersEqualsVariable())
			if (asn.isLoopIterator()) return true;
		return false;
	}
	
	public boolean isIteratorOf(IASTStatement loop) {
		if (loop instanceof IASTForStatement) return isIteratorOf((IASTForStatement) loop);
		return throwTodoException("unsupported loop");
	}
	
	public boolean isIteratorOf(IASTForStatement loop) {
		if (loop == null) return false;

		final ASTAddressable da = cacheRuntimeAddress();
		final VODCondGen cg = getCondGen();
		return (equalsVariable(fromCanonicalIteratorOf(loop, da, cg))
				|| equalsVariable(fromCanonicalInitializedIteratorOf(loop, da, cg)))
				&& new ASTRuntimeLocationComputer(cg).isIn(getTopNode(), loop); 
	}

	public boolean hasPrivateIterator() {
		if (isArray()) 
			for (Assignable<?> arg : getArguments()) 
				if (arg.isThreadPrivate()) return true;
		
		return false;
	}


	
	/**
	 * @param asn2
	 * @return true if this L-value <em>exclusively</em> before {@code asn2} 
	 * 	in file location
	 */
	public Boolean isBefore(final Assignable<?> asn2) 
			throws IncomparableException {
		return guard(()-> compareTo(asn2) < 0,
				()-> null,
				asn2);
	}
	
	/**
	 * Faster comparison of L-values without computing their global writing paths.
	 * 
	 * @param asn2
	 * @return true if this L-value exclusively before {@code lValue2} 
	 * 	in file location, given both of them appear in the same file.
	 */
	public Boolean isBeforeLocally(Assignable<?> asn2) {
		if (asn2 == null) throwNullArgumentException("assignable");
		return new ASTRuntimeLocationComputer(getCondGen())
				.isBeforeLocally(getTopNode(), asn2.getTopNode());
	}

	public Boolean isBeforeLocally(IASTNode node2) {
		if (node2 == null) throwNullArgumentException("assignable");
		return new ASTRuntimeLocationComputer(getCondGen())
				.isBeforeLocally(getTopNode(), node2);
	}
	
	/**
	 * Excluding the case that subject is the same as target.
	 * 
	 * @param asn2
	 * @return False could be either writes-after or in-comparableness.
	 */
	public Boolean writesBefore(Assignable<?> asn2) {
		try {
			return compareTo(asn2) < 0 && isAssigned();
		} catch (NullPointerException e) {	// thrown by && isAssigned()
		} catch (IncomparableException e) {	// thrown by compareTo(asn2)
		} catch (IllegalStateException e) { 
			throw e;
		} catch (Exception e) { 
			throwTodoException("unknown exceptions", e);
		}
		return null;
	}
	
	/**
	 * @param asn2
	 * @return
	 */
	public boolean isComparableTo(Assignable<?> asn2) {
		try { 
			compareTo(asn2);
			return true;
		} catch (IllegalArgumentException e) {
			return false;
		}
	}

//	public boolean isLocallyComparableTo(Assignable asn2) throws IncomparableException {
//		return isLocallyComparableTo(asn2, null);
//	}
//	
//	public boolean isLocallyComparableTo(Assignable asn2, String message, Method... callee) 
//			throws IncomparableException {
//		if (asn2 == null) throwNullArgumentException("ov");
//		if (equalsFile(asn2)) try {
//			compareLocallyTo(asn2);
//			return true;				// truly (valid) locally incomparable
//		} catch (Exception e) {
//			throwTodoException(e, "false locally incomparable alarm");
//		}
//		
//		if (message == null) message = "incomparable " + asn2;
//		getCondGen().log(null, message);
//		throwIncomparableException(asn2, message, callee);
//		return false;
//	}
	
	public boolean isContainedBy(IASTNode node) {
		return node != null && node.contains(getTopNode());
	}
	
	
	
	/**
	 * @return false if the assignable is used by any condition tester.
	 */
	public boolean isConditional() {
		return isConditional(false);	// !getBranchScopes().isEmpty()
	}

	/**
	 * @param isDirectly
	 * @return true if this assignable is accessed (written or read) dependently on the branch condition.
	 * @throws IllegalStateException
	 * @throws ASTException
	 */
	private boolean isConditional(final boolean isDirectly) {
		if (!hasBranchScopes()) return false;
		for (IASTStatement b : getBranchScopes()) {
			if (isConditionalTo(b)) return true;
			if (isDirectly) break;
		}
		
//		for (Assignable asgn : isDirectly ? getDirectAssigners() : getAssigners()) 
//			if (asgn.isConditional(isDirectly)) return true;
		return false;
	}
	
	public boolean isConditionalTo(IASTIfStatement branch) {
		if (branch == null) throwNullArgumentException("AST branch node");
		return !branch.getConditionExpression().contains(nameView) && 
				branch.contains(nameView);
	}
	
	@SuppressWarnings("unchecked")
	public boolean isConditionalTo(IASTForStatement branch) {
		if (branch == null) throwNullArgumentException("AST branch");
		
		/* iterator is bounded by loop condition, ex., 
		 * it++ starts from the lower-bound and stops at the upper-bound
		 */
		if (isIteratorOf(branch)) return true;

		enter(METHOD_IS_CONDITIONAL_TO);
		// a self-assigner is assigned in the second iteration
		if (selfAssigns() || isSelfAssigned()) 
			return leave(isContainedBy(branch), METHOD_IS_CONDITIONAL_TO);

		// checking direct conditional-ness first
		// asgr == this => asgr is neither iterator nor argument-conditional	
		for (Assignable<?> asgr : getDirectAssigners()) {
			if (asgr.enters(METHOD_IS_CONDITIONAL_TO)) 
				continue;
			if (asgr.isConditionalTo(branch)) 
				return leave(true, METHOD_IS_CONDITIONAL_TO);	
		}
		
		// for bypassing overridden getArguments()
		for (Assignable<?> arg : getArrayArguments()) {
			if (arg.enters(METHOD_IS_CONDITIONAL_TO)) 
				continue;
			if (arg.isConditionalTo(branch)) 
				return leave(true, METHOD_IS_CONDITIONAL_TO);	
		}
		
		// then checking indirect conditional-ness 
		for (Assignable<?> asgr : getAssigners()) {
			if (asgr.enters(METHOD_IS_CONDITIONAL_TO)) 
				continue;
			if (asgr.isConditionalTo(branch)) 
				return leave(true, METHOD_IS_CONDITIONAL_TO);	
		}
		
		for (Assignable<?> arg : (Set<Assignable<?>>) guard(()-> getArguments(), ()-> Collections.emptySet())) {
			if (arg.enters(METHOD_IS_CONDITIONAL_TO)) 
				continue;
			if (arg.isConditionalTo(branch)) 
				return leave(true, METHOD_IS_CONDITIONAL_TO);	
		}
		
		// !isAssigned() => isAssigned() outside this loop
		return leave(false, METHOD_IS_CONDITIONAL_TO);	
		
//		return !branch.getInitializerStatement().contains(nameView) &&	// both initializer and condition are global
//				!branch.getConditionExpression().contains(nameView) &&
	}
	
	public boolean isConditionalTo(IASTWhileStatement branch) {
		if (branch == null) throwNullArgumentException("AST branch node");

		// a self-assigner is assigned in the second iteration
		if (selfAssigns()) return true;
		
		return !branch.getCondition().contains(nameView) &&
				branch.contains(nameView);
	}
	
	public boolean isConditionalTo(IASTDoStatement branch) {
		if (branch == null) throwNullArgumentException("AST branch node");
		
		// a self-assigner is assigned in the second iteration
		if (selfAssigns()) return nextLocallyAssigned().isConditionalTo(branch);
		
		return !branch.getCondition().contains(nameView) &&
				branch.contains(nameView);
	}
	
	public boolean isConditionalTo(IASTStatement branch) {
//		if (testsNot(isAssigned())) return false;
		
		if (branch instanceof IASTIfStatement) return isConditionalTo((IASTIfStatement) branch);
		if (branch instanceof IASTForStatement) return isConditionalTo((IASTForStatement) branch);
		if (branch instanceof IASTWhileStatement) return isConditionalTo((IASTWhileStatement) branch);
		if (branch instanceof IASTDoStatement) return isConditionalTo((IASTDoStatement) branch);
		return branch == null 
				? throwNullArgumentException("AST branch node")
				: throwTodoException("unsupported branch type");
	}
	
	/**
	 * @return false if the assignable is used by the current condition tester.
	 */
	public boolean isDirectlyConditional() {
		return isConditional(true);
//		return debugCallDepth(()-> isConditional(true));
	}
	
	
	
	public Boolean isDirectlyConstant() {
		return cacheConstant(true);
	}
	
	@Override
	protected Boolean cacheConstant() {
		return get(
				()-> isDirectlyConstant(), 
				e-> cacheConstant(false));
	}
	
	private Boolean cacheConstant(boolean isDirectly) {
		if (nameView != null) {
			IBinding bind = ASTUtil.getBindingOf(nameView);
			if (bind instanceof IVariable) {
				IType type = ((IVariable) bind).getType();
				if (type instanceof IQualifierType 
						&& ((IQualifierType) type).isConst())
					return true;
			}
		}
		
		if (enters(METHOD_CACHE_CONSTANT)) return null;
		enter(METHOD_CACHE_CONSTANT);
		
		try {
		final VODCondGen cg = getCondGen();
		if (isLoopIteratingIterator()) return leave(
				ExpressionRange.fromIteratorOf(getEnclosingCanonicalLoop(), cacheRuntimeAddress(), cg).isConstant(), 
				METHOD_CACHE_CONSTANT);
		
		if (tests(isAssigned())) {
			if (selfAssigns()) return leave(false, METHOD_CACHE_CONSTANT);
			if (isLoopConditional()) {
				// assigned is shared and assigner is loop-conditional
				if (!isArray()) return leave(false, METHOD_CACHE_CONSTANT);
//				// Functionally self-assigning: norm_temp1[j] = norm_temp1[j] + x'
//				for (IASTStatement loop : getDependingLoops())
//					if (loop instanceof IASTForStatement) {
//						if (ASTLoopUtil.isConstant((IASTForStatement) loop, cg)) 
//							return leave(true, METHOD_CACHE_CONSTANT);
//					} else throwTodoException("unsupported loop");
			}
			
			final Expression asner = getAssigner();
			return leave(asner == null ? false : asner.isConstant(), METHOD_CACHE_CONSTANT);
		}
		
		final NavigableSet<Assignable<PV>> pras = previousRuntimeAssigneds();
		return pras.size() == 1 
				? leave(pras.first().isConstant(), METHOD_CACHE_CONSTANT)	// isConstant() may be null
				: leave(false, METHOD_CACHE_CONSTANT);
		
//		if (isConditional() && !hasMutexBranch()) 
//			return leave(false, METHOD_CACHE_CONSTANT);
		
//		if (tests(isFunctional(isDirectly))) 
//			return leave(false, METHOD_CACHE_CONSTANT);
		
//		final Set<Assignable<?>> asgns = isDirectly ? 
//				getDirectAssigners() : getAssigners();
//		assert asgns != null;
//		if (asgns.isEmpty()) 
//			return leave(getFirstAssignment() != null, METHOD_CACHE_CONSTANT);		// literal assignable
//		else for(Assignable<?> asgn : asgns) {
//			if (equalsVariable(asgn)) return leave(false, METHOD_CACHE_CONSTANT);	// self assignment
//			final Boolean subIsC = asgn.isConstant();
//			if (subIsC == null || !subIsC) return leave(subIsC, METHOD_CACHE_CONSTANT);
//		}
//
//		} catch (ASTException | IncomparableException e) {					
			// thrown by getDirectAssigners() | previousRuntimeAssigned()
		} catch (UncertainException e) {	
			// thrown by indirect (non-self) recursive call
			return leave((Boolean) null);
		} catch (Exception e) {	
			return throwUnhandledException(e, METHOD_CACHE_CONSTANT);
		}
	}
	

	
	@Override
	protected Boolean cacheGlobal() {
		return ASTUtil.isGlobal(nameView);
	}
	

	
	/**
	 * @see java.util.Comparator#compare(java.lang.Object, java.lang.Object)
	 */
	@Override
	public int compare(Assignable<?> asn1, Assignable<?> asn2) {
		if (asn1 == asn2) return 0;
		if (asn1 == null) asn2.throwIncomparableException(null);	// lv2 != null
		
		return asn1.compareTo(asn2);
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Comparable#compareTo(java.lang.Object)
	 */
	@Override
	public int compareTo(Assignable<?> asn2) throws IncomparableException {
		if (asn2 == null) throwIncomparableException(asn2);

		Integer result = COMPARE_CACHE.get(this, asn2);
		if (result != null) return result;
		result = COMPARE_CACHE.get(asn2, this);
		if (result != null) return -result;
		
		try {
			result = compareLocallyTo(asn2);	// truly (valid) locally incomparable
		
		} catch (NullPointerException | IllegalArgumentException e1) { 
			try2: try {
				// partly (valid) locally incomparable
				if (equalsVariable(asn2)) {
					if (previous != null) {
						result = comparePreviousTo(asn2);
						if (result != null) break try2;
					}
					if (asn2.previous != null) {
						result = compareNextTo(asn2);
						if (result != null) break try2;
					}
				}
				
				final VariableOrientedDag vop1 = VariableOrientedDag.from(this, getCondGen()),
						vop2 = VariableOrientedDag.from(asn2, getCondGen());
				if (vop1 == null || vop2 == null) throwIncomparableException(asn2);
				result = vop1.compareTo(vop2);
				
			} catch (ASTException | NullPointerException | IllegalStateException e2) {
				final VODCondGen cg = getCondGen();
				if (equalsFile(asn2) && equalsFile(cg.getTargetVariable())) 
					throwTodoException("false locally incomparable alarm", e2);
				
				final String message = "Incomparable " + asn2;
				cg.log(null, message, monitor);
				throwIncomparableException(asn2, message, e2);
				
			} catch (Exception e2) {
				/* all other exceptions like CoreException and InterruptedException  
				 * means unknown ones
				 */
				throwTodoException("unknown exceptions in comparing assignables: " + 
						this + " and\n\t" + asn2, e2); 
			}
		} 
		COMPARE_CACHE.put(this, asn2, result);
		return result;
	}

	public int compareLocallyTo(Assignable<?> asn2) 
			throws IllegalArgumentException {
		return ASTRuntimeLocationComputer.compareLocally(
				getASTName(), asn2.getASTName());
	}
	
	/**
	 * @param asn2
	 * @return null if reentering.
	 */
	private Integer comparePreviousTo(final Assignable<?> asn2) {
		return compareLinkedlyTo(asn2, true);
//		return debugCallDepth(()-> compareLinkedlyTo(asn2, true));
	}
	
	/**
	 * @param asn2
	 * @return null if reentering. 
	 */
	private Integer compareNextTo(final Assignable<?> asn2) {
		return compareLinkedlyTo(asn2, false);
	}
	
	/**
	 * @param asn2
	 * @param linksPrevious
	 * @return null if reentering. 
	 */
	private Integer compareLinkedlyTo(
			final Assignable<?> asn2, final boolean linksPrevious) {
		assert asn2 != null && asn2 != this;
		return guard(()-> {
			final Assignable<?> link2 = linksPrevious ? 
					asn2.previous() : asn2.next();
					if (link2 == null) return null;
					if (link2 == this) return linksPrevious ? -1 : 1;
					return compareLinkedlyTo(link2, linksPrevious);
		},
				()-> null,
				e-> e instanceof IncomparableException ? 
						null : throwUnhandledException(e),
				asn2,
				linksPrevious);
	}
	
	
	
	@Override
	public boolean derives(Addressable address2) {
		final boolean sd = VersionEnumerable.super.derives(address2);
		if (sd) return true;
		
		if (address2 instanceof Assignable) {
			final Assignable<?> asn2 = (Assignable<?>) address2;
			final Boolean isA = isAssigned(), isA2 = asn2.isAssigned();
			if (isA == null || isA2 == null) return sd;
			if (isA && isA2) return sd;
			
			if (!isA && isA2) return previousRuntimeAssigneds().contains(asn2);
			
			final Collection<? extends Addressable> pras2 = asn2.previousRuntimeAssigneds();
			if (isA && !isA2) return pras2.contains(this);
			for (Addressable pra2 : pras2) if (derives(pra2)) return true;
		}
		return sd;
	}

	public boolean equalsFile(Assignable<?> asn2) {
		if (asn2 == null) throwNullArgumentException("assignable");
		return getFileLocation().getFileName().equals(asn2.getFileLocation().getFileName());
	}
	
	public boolean equalsVariable(Assignable<?> lv2) {
		return lv2 != null && nameView != null 
				&& ASTUtil.equals(nameView, lv2.getASTName(), true);
		
//		IName nameDef = ASTUtil.getDefinitionOf(nameView);
//		if (nameDef == null) return false;
//		else return nameDef.equals(ASTUtil.getDefinitionOf(lv2.getName()));
	}

	@SuppressWarnings("unchecked")
	public boolean equalsVariable(PathVariable pv) {
		// getPathVariable() may return null
		return pv != null && PathVariable.from((Assignable<PathVariable>) this).equals(pv);
	}
	
	public boolean equalsVariable(PathVariablePlaceholder pvp) {
//		return pvp != null && pvp.getAssignable() == this;
		return pvp != null && equalsVariable(pvp.getVariable());
	}
	
	protected boolean equalsString(Assignable<?> asn2) {
		return asn2 != null
				&& toString().equals(asn2.toString());
	}
	
	/**
	 * Serialization-based equivalence and hashing.
	 * 
	 * @param e2
	 * @return
	 */
	@Override
	protected boolean equalsToCache(SystemElement e2) {
		return toString().equals(((Assignable<?>) e2).toString());
//		return compareTo((Assignable) e2) == 0;
//			return nameView != null && ASTUtil.equals(nameView, ((LValue) lv).getName());
//		else if (obj instanceof IASTName) 
//			return nameView != null && nameView.equals(obj);
//		else if (obj instanceof IASTExpression) 
//			return expView != null && expView.equals(obj);
//		else 
//			return super.equals(e2);
	}
	
	/**
	 * Serialization-based equivalence and hashing.
	 * 
	 * @see ompca.vodcg.SystemElement#hashCodeVars()
	 */
	@Override
	protected List<Integer> hashCodeVars() {
		assert toString() != null;
		return Arrays.asList(toString().hashCode());
//		return ((nameView != null) ? nameView.hashCode() : 0) 
//				+ ((expView != null) ? expView.hashCode() : 0) 
//				+ super.hashCode();
	}

	

	@SuppressWarnings("unchecked")
	@Override
	public void reversion(Version<? extends PV> newVersion) {
		try {
			VersionEnumerable.super.reversion(newVersion);
			PathVariable.reversion((Assignable<PathVariable>) this, newVersion);
			
		} catch (Exception e) {
			throwTodoException(e);
		}
	}

	@Override
	public void setVersion(Version<? extends PV> newVersion) {
		getPathVariablePlaceholder().setVersion(newVersion);
	}

//	public Version<? extends PathVariable> cloneReversion(
//			final IASTStatement blockStat, final ThreadRole role, Version<? extends PathVariable> ver) 
//					throws NoSuchVersionException {
//		Version<? extends PathVariable> rever = ver;
//		if (blockStat != null) try {
//			if (role != null) switch (role) {
//			case CONST:
//			case MASTER:
//			case NON_MASTER:
//				DebugElement.throwTodoException("unsupported role");
//			case FUNCTION:
//				rever = ver != null && ver.getAssignable() == this
//				? ver
//				: FunctionalVersion.from(this, blockStat);
//				break;
//			default:
//			}
//			
//		} catch (NoSuchVersionException e) {
//		}
//		
//		if (rever != null) {
//			reversion(rever);
//			return rever;
//		}
//		return getVersion(role);
////		return throwTodoException("in-reversionnable assignable");
//	}
	
	
	
	@SuppressWarnings("unchecked")
	@Override
	public Assignable<PV> previous() throws IncomparableException {
		return previous(!tests(isGlobal()));
	}
	
	/**
	 * @return the previous assignable equals name in locality, 
	 * 	not necessarily an l-value.
	 * 	May return null if this assignable is a local parameter, 
	 * 	which may have multiple (ambiguous) calling arguments.
	 */
	public Assignable<PV> previous(final boolean findsLocally) 
			throws IncomparableException {
		if (isParameter() || isDeclarator()) return null; 
		if (previous != null) return previous;

		final Boolean isG = isGlobal();
		final Assignable<PV> p = previousOrNext(
				getWritingFunctionDefinition(), false, findsLocally);
		if (!(tests(isG) && findsLocally)) setPrevious(p);
		if (p == null && testsNot(isG)) 
			throwTodoException("uninitialized non-parameter/variable");
		return p;
	}
	
	/**
	 * @param root
	 * @param findsNext
	 * @param findsLocally
	 * @return the previous or next assignable of same path variable
	 * @throws IncomparableException
	 */
	@SuppressWarnings("unchecked")
	protected Assignable<PV> previousOrNext(
			IASTNode root, final Boolean findsNext, Boolean findsLocally) 
			throws IncomparableException {
		if (root == null) return null;
		if (isDeclarator() && testsNot(findsNext)) return null;
		
		Assignable<PV> pOrN = null;
//		/* isGlobal or isGlobal == null
//		 * for a global variable may be accessed via some indirect local calls
//		 */
//		if (!testsNot(isGlobal())) findsLocally = false;	
		final NavigableSet<Assignable<?>> asns = fromOf(root, getName(), null, getCondGen());
		pOrN = (Assignable<PV>) (tests(findsNext) ? asns.higher(this) : asns.lower(this));

//		final boolean findsAny = findsNext == null && findsLocally == null;
//		for (Assignable<?> current : fromOf(root, getName(), null, getCondGen())) {
//			assert equalsVariable(current);
//			final boolean inc = current != this;
//			if (findsAny) {
//				if (inc) return (Assignable<PV>) current;
//				continue;
//			}
//			if (!current.isRuntimeTraversable()) continue;
//			
//			/*
//			 * this < current < pOrN	=>	pOrN = current if	findsNext && ibc && cbp
//			 * this < pOrN < current	=>	pOrN = current if 	findsNext && ibc && pOrN == null
//			 * pOrN < this < current	=>	pOrN = X
//			 * pOrN < current < this	=>	pOrN = current if 	!findsNext && !ibc && !cbp
//			 * current < pOrN < this	=>	pOrN = current if 	!findsNext && !ibc && pOrN == null
//			 * current < this < pOrN	=>	pOrN = X
//			 */
//			final Boolean ibc = isBefore(current);
//			if (ibc == null) throwIncomparableException(current);
//			if (findsNext ? ibc : !ibc && inc) {
//				if (pOrN == null) pOrN = (Assignable<PV>) current;
//				else {
//					final Boolean cbp = current.isBefore(pOrN);
//					if (cbp == null) throwIncomparableException(pOrN);
//					if (findsNext ? cbp : !cbp) pOrN = (Assignable<PV>) current;
//				}
//			}
//			else continue;
//		}
		
		if (tests(findsLocally)) return pOrN;
		final Assignable<PV> npOrN =
				previousOrNext(root.getParent(), findsNext, findsLocally);
		return npOrN == null ? pOrN : npOrN;
	}
	
	/**
	 * for non-lv's:
	 * 1) plv = ... this ... -> previousAssigned() := plv's previousAssigned()
	 * 2) plv == null -> this isn't initialized;
	 *  
	 * @return the previously assigned assignable <em>at runtime (not syntactically)</em>.
	 */
//	@Override
	@SuppressWarnings("unchecked")
	public Assignable<PV> previousAssigned() 
			throws ASTException, IncomparableException, UncertainPlaceholderException {
		Assignable<PV> plv = null;
		if (tests(()-> isGlobal() && isConstant())) {
			final IASTFunctionDefinition f = ASTUtil.getWritingFunctionDefinitionOf(getTopNode()); 
			if (f == null) return null;			// f is in a global declarator
					
			final VODCondGen cg = getCondGen();
			for (Assignable<?> lv : cg.getWritingHistoryOfBeforeTP(this)) {	
				// lv.isAssigned()
				final IASTFunctionDefinition lvf = 
						ASTUtil.getWritingFunctionDefinitionOf(lv.getTopNode());
				if (lvf == null) return (Assignable<PV>) lv;	// lv is globally initialized
				if (f == lvf) {
					if (tests(lv.isBeforeLocally(this))) return (Assignable<PV>) lv;
				} else {
					if (cg.isMainFunction(lvf)) return (Assignable<PV>) lv;
					if (plv == null || tests(lv.isBefore(plv))) plv = (Assignable<PV>) lv;
				}
			}
			return plv; // throwTodoException("unsupported global constant");
		}
		
		// 2) plv == null -> this isn't initialized;
		plv = previous();
		if (plv == null) return null;
		
		// 1) plv = ... this ... -> previousAssigned() := plv's previousAssigned()
		do {
			final Boolean pia = plv.isAssigned();
			if (pia == null) throwUncertainPlaceholderException("pia == null");
			if (pia && !isDirectlyAssigningTo(plv)) break;
			plv = plv.previous();
		} while (plv != null);
		return plv;
	}
	
	/**
	 * @return @NotNull
	 */
	@SuppressWarnings("unchecked")
	@Override
	public NavigableSet<Assignable<PV>> previousRuntimes() 
			throws ASTException, IncomparableException, UncertainPlaceholderException {
		if (isDeclarator() || isParameter()) return Collections.emptyNavigableSet();
		
		// checking mutex assigned before iterated assigned
		final NavigableSet<Assignable<PV>> mas = getMutexAssigneds();
		if (!mas.isEmpty()) return mas;
		
		final Assignable<PV> pAsn = previous();
		if (pAsn != null) {
			mas.add(pAsn);
			if (pAsn.isDeclarator() || pAsn.isParameter()) return mas;
			
//			final Assignable pmAsn = MutexAssignedVersion
//					.from(pAsn, pAsn.getPathVariablePlaceholder().getThreadRole())
//					.previousRuntimeOf(pAsn);
//			if (pmAsn != null) return pmAsn;
			
//			final FunctionalVersion fv = FunctionalVersion.from(pAsn);
			if (hasSameIterationAs(pAsn)) return mas;
		}
		
		final Assignable<PV> nAsn = next(true);
		if (nAsn != null && hasSameIterationAs(nAsn)) mas.add(nAsn);
		
		return mas;
	}
	
//	/**
//	 * @return previous AST assigned assignable if it's unconditionally assigned 
//	 * 	since all later conditional accesses are read-only.
//	 * @throws ASTException
//	 * @throws IncomparableException
//	 * @throws UncertainPlaceholderException
//	 */
//	@SuppressWarnings("unchecked")
//	@Override
//	public NavigableSet<Assignable> previousRuntimeAssigneds() 
//			throws ASTException, IncomparableException, UncertainPlaceholderException {
////		final Assignable pAsd = previousAssigned();
//		NavigableSet<Assignable> prs = previousRuntimes();
//		final Set<Assignable> pras = new HashSet<>();
//		while (prs != null && !tests(prs.isAssigned())) 
//			prs = pras.add(prs) 
//					? prs.previousRuntimes()
//					: prs.previous();	// pAsn re-occurred due to loop
//		return prs;
//	}
	
	/**
	 * @return the latest effective assigner
	 */
	public Expression previousAssigner() {
//		Assignable preLv = this;
//		if (isAssigning()) {
//			final SortedSet<Assignable> preLvs = getWritingHistoryBefore().headSet(this);
//			if (preLvs.isEmpty()) 
//				Debug.throwTodoException("Non-constant variable?");
//			preLv = preLvs.last(); 
//		}
		try {
			return Elemental.getSkipNull(()-> previousAssigned().getAssigner());
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	
	/**
	 * @return the next assignable equals name in locality, not necessarily an l-value
	 */
	public Assignable<PV> next() 
			throws IncomparableException {
		return next(!tests(isGlobal()));
	}
	
	public Assignable<PV> next(final boolean findsLocally) 
		throws IncomparableException {
		final Assignable<PV> next = previousOrNext(
				getWritingFunctionDefinition(), true, findsLocally);
		if (next != null && !(tests(isGlobal()) && findsLocally)) {
			final Assignable<PV> np = next.previous();
			if (np == null) next.setPrevious(this);
			else if (np != this && next.getClass() != np.getClass()) 
				throwTodoException("inconsistent previous assignables");
		}
		return next;
	}
	
	/**
	 * for non-lv's:
	 * 1) plv = ... this ... -> nextAssigned() := plv
	 * 
	 * TODO? nextRuntimeAssigned()
	 * 
	 * @return
	 */
	public Assignable<PV> nextLocallyAssigned() 
			throws ASTException, IncomparableException {
		// 1) plv = ... this ... -> nextAssigned() := plv
		Assignable<PV> plv = previous(true);
		final Assignment asm = getFirstAssignment();
		while (plv != null) {
			final Assignment pAsm = plv.getFirstAssignment();
			if (pAsm == null || !pAsm.equals(asm)) break;
			
			final Boolean pia = plv.isAssigned();
			if (pia == null) throwUncertainException("pia == null");
			if (pia) {
				if (isDirectlyAssigningTo(plv)) return plv;
				else break;
			}
			plv = plv.previous(true);
		} 
		
		Assignable<PV> nlv = next(true);
		while (nlv != null) {
			final Boolean nia = nlv.isAssigned();
			if (nia == null) throwUncertainException("nia == null");
			if (nia) break;
			nlv = nlv.next(true);
		}
		return nlv;
	}

	public IASTReturnStatement nextReturnStatement() {
		return ASTUtil.nextReturnStatementTo(getTopNode());
	}
	
	public Assignable<PV> nextEqualsVariable() {
		Assignable<PV> next = this;
		while ((next = next.next(true)) != null && next.equalsVariable(this)) return next;
		return null;
	}
	
	public Assignable<PV> elseEqualsVariable() {
		return previousOrNext(getWritingFunctionDefinition(), null, null);
	}
	

	
	/**
	 * @return
	 */
	public IASTExpression toASTExpression() {
		return expView;
	}
	
	/**
	 * @param asns
	 * @return a non-null expression list
	 */
	public static List<? extends Expression> toExpressions(List<Assignable<?>> asns) {
		return toPlaceholders(asns);
	}
	
	/**
	 * @param asns
	 * @return a non-null placeholder list
	 */
	public static List<PathVariablePlaceholder> toPlaceholders(List<Assignable<?>> asns) {
		final List<PathVariablePlaceholder> es = new ArrayList<>();
		if (asns != null) for (Assignable<?> asn : asns)
			es.add(asn.getPathVariablePlaceholder());
		return es;
	}
	
	@SuppressWarnings("unchecked")
	@Override
	protected Assignable<PV> toConstantIf() throws ASTException, UncertainException {
		assert previousRuntimeAssigneds().size() == 1;
		return testsSkipNull(isAssigned(), 
				()-> this, 
				()-> get(()-> 
				((Assignable<PV>) previousRuntimeAssigneds().first()).toConstantIf(), ()-> this, null));
	}
	
	final public FunctionalAssignable toFunctional() {
		assert !(this instanceof FunctionalAssignable);	// since FunctionalAssignable overrides this
		return tests(isFunctional())  
				? toFunctionalIf()
				: null;
	}
	
	protected FunctionalAssignable toFunctionalIf() {
		final IBinding asnBind = getBinding();
		Map<IASTName, Assignable<?>> varBindLvs = ASSIGNABLE_CACHE.get(asnBind);
		
		final IASTName name = getASTName();
		if (varBindLvs == null) 
			ASSIGNABLE_CACHE.put(asnBind, varBindLvs = new HashMap<>());
		else {
			final Assignable<?> oldAsn = varBindLvs.get(name);
			if (oldAsn instanceof FunctionalAssignable) return (FunctionalAssignable) oldAsn;
		}

		@SuppressWarnings("unchecked")
		final FunctionalAssignable fasn = new FunctionalAssignable((Assignable<PathVariable>) this);
		varBindLvs.put(name, fasn);
		
		// check ubiquitous
		for (Assignable<PV> asn : getOthersEqualsVariable())	// asn != this
			if (asn.toFunctional() == null) throwTodoException("inconsistent assignable's");
		return fasn;
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return nameView == null 
				? bindingView.getName() : ASTUtil.toStringOf(nameView);
	}

}