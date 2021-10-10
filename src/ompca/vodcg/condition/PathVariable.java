/**
 * 
 */
package ompca.vodcg.condition;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.NavigableSet;
import java.util.Set;
import java.util.TreeSet;

import org.eclipse.cdt.core.dom.ast.IASTArrayDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IBinding;
import org.eclipse.cdt.core.dom.ast.IVariable;

import ompca.Elemental;
import ompca.vodcg.ASTAddressable;
import ompca.vodcg.ASTException;
import ompca.vodcg.ASTUtil;
import ompca.vodcg.Assignable;
import ompca.vodcg.IncomparableException;
import ompca.vodcg.SystemElement;
import ompca.vodcg.UncertainException;
import ompca.vodcg.UncertainPlaceholderException;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.data.DataType;
import ompca.vodcg.condition.data.PlatformType;
import ompca.vodcg.condition.version.ConstantCountingVersion;
import ompca.vodcg.condition.version.EnumeratedVersion;
import ompca.vodcg.condition.version.NoSuchVersionException;
import ompca.vodcg.condition.version.ThreadRole;
import ompca.vodcg.condition.version.Version;

/**
 * An l-value based memory address history mapping.
 * 
 * @author Kao, Chen-yi
 *
 */
public class PathVariable extends Variable {

	private static final Map<Assignable<? extends PathVariable>, PathVariable> PV_REGISTRY = 
			Collections.synchronizedMap(new HashMap<>());

	static private final Method METHOD_CACHE_SCOPE = 
			Elemental.getMethod(PathVariable.class, "cacheScope");
	static private final Method METHOD_FROM = 
			Elemental.getMethod(PathVariable.class, "from", Assignable.class);

	
	
	private final Set<Assignable<? extends PathVariable>> asns = new HashSet<>();
	
	/**
	 * Non-registering constructor.
	 * 
	 * @param asn
	 * @param scope - pre-cached function scope for some function parameter var 
	 * if provided
	 * @throws IllegalArgumentException
	 */
	protected PathVariable(Assignable<? extends PathVariable> asn, Function scope) throws IllegalArgumentException {
		super(asn.getASTName(), asn.getBinding(), asn.cacheRuntimeAddress(), asn.getCondGen());
		
		// reusable to sub-classes
		addAssignable(asn);
		
		if (scope != null) {
			setScope(()-> scope);
			setFunctionScope(()-> scope);
		}
	}
	
//	/**
//	 * Handling multi-level pointer (multi-dimension array)?
//	 * 
//	 * @param lValue
//	 * @param scope
//	 * @throws IllegalArgumentException
//	 * @throws CoreException
//	 * @throws InterruptedException
//	 */
//	protected PathVariable(IASTUnaryExpression lValue, ConditionElement scope) 
//			throws IllegalArgumentException, CoreException, InterruptedException {
//		this(LValue.from(lValue), scope);	// no try-catch block surrounding allowed
//		type = DataType.Pointer; 
//	}

	/**
	 * Copy constructor for {@link FunctionalPathVariable} or other sub-classes.
	 * 
	 * @param pv
	 */
	protected PathVariable(PathVariable pv) {
		super(pv.getIName(), pv.getType(), pv.cacheRuntimeAddress(), pv.getScopeManager());

		// reusable to sub-classes
		for (Assignable<? extends PathVariable> asn : pv.asns) addAssignable(asn);
		setFunctionScope(()-> pv.getFunctionScope());
	}



//	/**
//	 * TODO: PathVariableDiscover	extends ASTGenericVisitor
//	 * 
//	 * @param exp - needs to check if it's {@link IASTNameOwner}, the l-value container.
//	 * @param condGen 
//	 * @param seProps
//	 * @return
//	 * @throws CoreException 
//	 * @throws InterruptedException 
//	 */
//	public static PathVariable from(IASTExpression exp, VOPCondGen condGen) 
//			throws CoreException, InterruptedException {
//		LValue lv = LValue.from(ASTLValueComputer.getVariableNameOf(exp), condGen);
//		PathVariable pv = from(lv);
//		return FunctionalPathVariable.getIfParsingArray(pv, lv);
//	}

	/**
	 * @param declarator
	 * @param rtAddr 
	 * @param condGen
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public static PathVariable from(IASTDeclarator declarator, final ASTAddressable rtAddr, VODCondGen condGen) {
		try {
		final Assignable<? extends PathVariable> asn = Assignable.from(declarator, rtAddr, condGen);
		return (declarator instanceof IASTArrayDeclarator) 
				? FunctionalPathVariable.from(
						(IASTArrayDeclarator) declarator, (Assignable<FunctionalPathVariable>) asn, (PathVariable) null)
				: from((Assignable<PathVariable>) asn);
				
		} catch (ClassCastException e) {
			return throwTodoException(e);
		}
	}
	
	
	
	public static <PV extends PathVariable> PV from(Assignable<PV> asn) {
		return from(asn, null);
	}
	
	/**
	 * @param asn
	 * @param scope - pre-cached function scope for some function parameter var
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public final static <PV extends PathVariable> PV from(Assignable<PV> asn, Function scope) {
		if (asn == null) throwNullArgumentException("assignable");

		// getPathVariable() may call PathVariable(asn) or functional (lazy) getSubject()
		PV pv = null;
//		try {
//			pv = asn.getPathVariableDelegate().getVariable();
//			if (pv != null) return pv;
//		} catch (IllegalStateException e) {
//			if (!isUncertainDelegateException(e)) throw e;
//		}

		pv = (PV) PV_REGISTRY.get(asn);
		if (pv != null) return pv;

		for (Assignable<? extends PathVariable> key : PV_REGISTRY.keySet()) if (key.equalsVariable(asn)) {
			pv = (PV) PV_REGISTRY.get(key);
			break;
		}
		
		if (pv == null && !asn.enters(METHOD_FROM)) {
			asn.enter(METHOD_FROM); NonRegisteredAsns: {
			final Set<Assignable<PV>> as = asn.getOthersEqualsVariable();
			for (Assignable<PV> a : as) try {
				pv = a.getPathVariable();
				if (pv != null) break NonRegisteredAsns;
			} catch (IllegalStateException e) {
				continue;
				
			} catch (ClassCastException e) {
				throwTodoException(e);
			}

			final Assignable<PV> easn = asn.elseEqualsVariable();
//			final Assignable asgd = asn.getAssigned();	// PathVariable is assignment dependent
			if (easn != null) pv = easn.getPathVariable();
//		} catch (IllegalStateException e) {
//			if (!isUncertainDelegateException(e)) throw e;
//		} finally {
			} asn.leave(METHOD_FROM);
		}
		
		if (pv != null) {pv.addAssignable(asn); return pv;}
		return (PV) new PathVariable(asn, scope);
	}


	
	/**
	 * @param var
	 * @param scope - pre-cached function scope for some function parameter var
	 * @param condGen 
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public static PathVariable from(IVariable var, Function scope, VODCondGen condGen) {
		if (var == null) throwNullArgumentException("variable");
		if (scope == null) throwNullArgumentException("function scope");
		
		IASTName varAst = ASTUtil.getNameOfFrom(var, scope.getIName());
		// var != null && varAst == null => var is in external libraries
		try {
		return from((Assignable<PathVariable>) (varAst == null ? 
				Assignable.from(var, condGen) : Assignable.from(varAst, scope.cacheRuntimeAddress(), condGen)), 
				scope);
		
		} catch (ClassCastException e) {
			return throwTodoException(e);
		}
	}
	


	@SuppressWarnings("unchecked")
	public static PathVariable getIteratorOf(IASTForStatement loop, final ASTAddressable rtAddr, VODCondGen condGen) {
		try {
		return from((Assignable<PathVariable>) Assignable.fromCanonicalIteratorOf(loop, rtAddr, condGen));
		
		} catch (ClassCastException e) {
			return throwTodoException(e);
		}
	}
	
	
	
	public boolean isIteratorOf(IASTForStatement forLoop) {
		for (Assignable<? extends PathVariable> asn : getAssignables())
			if (asn.isIteratorOf(forLoop)) return true;
		return false;
	}
	
	public boolean isLoopIterator() {
		for (Assignable<? extends PathVariable> asn : getAssignables())
			if (asn.isLoopIterator()) return true;
		return false;
	}
	
	
	
	protected boolean addAssignable(Assignable<? extends PathVariable> asn) {
		assert asn != null;
		PV_REGISTRY.put(asn, this);
//		asn.setPathVariableDelegate();
		for (Assignable<? extends PathVariable> a : asns) 
			if (a.getBinding() != asn.getBinding()) throwTodoException("true equivalence");
		return asns.add(asn);
	}
	
	/**
	 * @return non-null
	 */
	public Set<Assignable<? extends PathVariable>> getAssignables() {
		return asns;
	}
	
	public NavigableSet<Assignable<? extends PathVariable>> sortAssignables() {
		NavigableSet<Assignable<? extends PathVariable>> sortedLvs = null;
		
		for (Assignable<? extends PathVariable> lv : getAssignables()) {
			if (sortedLvs == null) sortedLvs = new TreeSet<>(lv);
//			if (sortedLvs == null) sortedLvs = 
//					Collections.synchronizedSortedSet(new TreeSet<>(lv));
			try {sortedLvs.add(lv);
			} catch (IllegalArgumentException | NullPointerException e) {continue;}
		}
		
		return sortedLvs;
	}
	


	/**
	 * @return C name in {@link IASTName} form.
	 */
	public IASTName getASTName() {
		IASTName aName = super.getASTName();
		if (aName != null) return aName;
		
		asns.addAll(asns.iterator().next().getOthersEqualsVariable());
		for (Assignable<? extends PathVariable> a : asns) {
			aName = a.getASTName();
			if (aName != null) {setName(aName); break;}
		}
		return aName;
	}

	@Override
	public PlatformType getType() {
		PlatformType type = super.getType();
		if (type == null) {
			IBinding bind = getASTName().getBinding();
			if (bind instanceof IVariable) 
				type = DataType.from(((IVariable) bind).getType());
			else throwTodoException("unsupported variable");

			setType(type);
		}
		return type;
	}

	

	@Override
	protected ConditionElement cacheScope() {
		ConditionElement scope = null;
		if (isParameter() && !enters(METHOD_CACHE_SCOPE)) {
			enter(METHOD_CACHE_SCOPE);
			scope = getFunctionScope();
			leave(METHOD_CACHE_SCOPE);
		} else {
			
			Assignable<? extends PathVariable> asn = sortAssignables().first();
			assert asn != null;
			scope = Function.from(asn.getWritingFunctionDefinition(), cacheRuntimeAddress(), asn.getCondGen());
			
//			if (cName instanceof IASTName) {
//				IBinding owner = ((IASTName) cName).resolveBinding();
//				while (owner != null) {
//					owner = owner.getOwner();
//					if (owner instanceof IFunction) {
//						scope = Function.get(owner.getName(), (IFunction) owner, condGen);
//						break;
//					}
//				}
//			} else	// TODO: scope = \/ lv.getWritingFunctionDefinition()
		}
		return scope;
	}

	
	
	/**
	 * An ID is said to be dependent on a loop only if it's a variable ID and the variable is either 
	 * the loop iterator or an array accessed (indexed) by the iterator through 
	 * the (subscript) arguments or pointer to the array.
	 *
	 * TODO: Supporting loops more than the canonical ones.
	 * 
	 * TODO: DependentVariableDiscover	extends ASTGenericVisitor
	 * TODO: SideEffectCollector		extends ASTGenericVisitor
	 * 
	 * @param asn - assumed a variable l-value
	 * @param loop
	 * @return The loop iterator wrapped as PV if there's dependency. Or null if there's not.
	 */
	public static PathVariable getDirectlyDependentOnBy(Assignable<PathVariable> asn, IASTForStatement loop) {
		final PathVariable by = from(asn);	// assert asn != null;
		final ASTAddressable rtAddr = asn.cacheRuntimeAddress();
		final VODCondGen condGen = asn.getCondGen();
		final Assignable<?> li = Assignable.fromCanonicalIteratorOf(loop, rtAddr, condGen);	// loop iterator
		if (asn.equals(li)) return by;
		
		// or an array accessed (indexed) by the loop iterator
		// through the (subscript) arguments or pointer to the array.
		else {
			IASTExpression lvExp = asn.toASTExpression();
			if (lvExp instanceof IASTArraySubscriptExpression) {
				FunctionalPathVariable apv = FunctionalPathVariable.fromRecursively(
						(IASTArraySubscriptExpression) lvExp, rtAddr, condGen);
				if (apv != null && apv.dependsOn(by)) return by;
			}
		}
		
		return null;
	}
	
	
	
	protected void cacheDirectSideEffect() {
		for (Assignable<? extends PathVariable> a : getAssignables())
			orSideEffect(()-> a.getConditions(null));
	}

	
	
	@Override
	protected Boolean cacheConstant() {
		if (asns.isEmpty()) return null;
		for (Assignable<? extends PathVariable> asn : new ArrayList<>(asns)) {
			Boolean aic = asn.isConstant();
			if (aic == null) return null;
			if (!aic) return false;
		}
		return true;
	}
	
	@Override
	protected <T extends SystemElement> T toConstantIf() throws ASTException, UncertainException {
		return asns.iterator().next().toConstant();
	}
	
	public boolean isParameter() {
		VODCondGen condGen = null;
		for (Assignable<? extends PathVariable> lv : getAssignables()) {
			if (lv.isParameter()) return true;
			if (condGen == null) condGen = lv.getCondGen();
		}
		return super.isParameter();
	}
	
	
	
	static public void versionWith(Assignable<PathVariable> lValue) 
			throws ASTException, IncomparableException, 
			UncertainPlaceholderException, NoSuchVersionException {
		if (lValue != null) 
			from(lValue).reversion(lValue);
	}
	
	static public void versionWith(Assignable<PathVariable> lValue, int revCount) 
			throws ASTException, IncomparableException, 
			UncertainPlaceholderException, NoSuchVersionException {
		if (lValue != null) 
			from(lValue).reversionTill(lValue, revCount);
	}
	
	static public void versionWith(Assignable<PathVariable> lValue, Function f) 
			throws ASTException, IncomparableException, 
			UncertainPlaceholderException, NoSuchVersionException {
		if (lValue != null) 
			from(lValue).reversion(lValue, f);
	}

//	static public void versionConstantlyWith(IASTName ov, IASTForStatement loop) {
//	PathVariable pv = get(ov);
//	pv.reversionConstantly(ov, loop);
//}
	
	public void reversion(Assignable<PathVariable> lv) 
			throws ASTException, IncomparableException, 
			UncertainPlaceholderException, NoSuchVersionException {
		if (lv == null) throwNullArgumentException("assignable");
		reversion(lv, EnumeratedVersion.from(
				lv, PathVariablePlaceholder.from(lv).getThreadRole()));
	}

	public void reversion(Assignable<PathVariable> lv, Function func) 
			throws ASTException, IncomparableException, 
			UncertainPlaceholderException, NoSuchVersionException {
		if (lv == null) throwNullArgumentException("assignable");
		if (func == null) throwNullArgumentException("function");
		reversion(lv);
	}

//	public void reversionConstantly(IASTName ov, IASTForStatement loop) {
//		Version oldVer = versions.get(ov), newVer = new ConstantCountingVersion(this, loop);
//		if (oldVer == null) versions.put(ov, newVer);
//		else oldVer.append(newVer);
//	}

	static public void reversion(
			Assignable<PathVariable> lv, Version<? extends PathVariable> newVersion) {
		PathVariablePlaceholder.from(lv).reversion(newVersion); 
	}
	
	/**
	 * ... 
	 * vLv	-> vLv_revCount 
	 * ... 
	 * lv	-> lv_revCount
	 * ... 
	 * vLv	-> vLv
	 * ... 
	 * 
	 * @param asn
	 * @param revCount
	 */
	public void reversionTill(Assignable<PathVariable> asn, int revCount) 
			throws ASTException, IncomparableException, 
			UncertainPlaceholderException, NoSuchVersionException {
		if (asn == null) throwNullArgumentException("assignable");
		
		boolean lvIsReversioned = false;
		final ConstantCountingVersion<PathVariable> ccv = 
				new ConstantCountingVersion<>(revCount, asn, ThreadRole.MASTER);
		for (Assignable<? extends PathVariable> pLv : getCondGen().getWritingHistoryOfBeforeTP(asn)) {
			lvIsReversioned = true;
			PathVariablePlaceholder.from(pLv).reversion(ccv);
		}
		
		// the delegate of lv is not created yet
		if (!lvIsReversioned) reversion(asn, ccv);
	}
	
	/**
	 * 
	 */
	public void reversionLoopIterator() {
		throwTodoException(getName() + "_?loop");
		setName(getName() + "_?loop");
	}
	
}