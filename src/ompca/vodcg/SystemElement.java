/**
 * 
 */
package ompca.vodcg;

import java.lang.reflect.Method;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

import ompca.CalleeCache;
import ompca.Cluster;
import ompca.Elemental;
import ompca.Pair;
import ompca.SupplierCluster;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public abstract class SystemElement extends DebugElement implements Elemental {

	private static final Method METHOD_EQUALS = 
			Elemental.getMethod(SystemElement.class, "equals", Object.class);
//	private static final Method METHOD_HASH_CODE = 
//			Elemental.getMethod(SystemElement.class, "hashCode");
//	private static final Method METHOD_IS_CONSTANT = 
//			getMethod(Element.class, "isConstant");
	private static final Method METHOD_TO_CONSTANT = 
			Elemental.getMethod(SystemElement.class, "toConstant");
	
	/**
	 * Clustering lambda instances since a lambda function may differ 
	 * in different caller stacks for even identical object instances.
	 */
	static final private Map<Pair<Cluster<Supplier<?>>, List<Object>>, Integer> INDEPENDENT_CALLEES = new HashMap<>();
	
	/**
	 * Null means either unknown or constant scope for this Element.
	 */
	private static VODCondGen CondGen	= null;
	
	private ASTAddressable runtimeAddress = null;
	
	private BigInteger hashCode = null;
//	private int hashCode = -1;
//	private int hashCodeOverflow = 0;
	
	final private List<SystemElement> eqList = new ArrayList<>();
//	final private List<Element> ieqList = new ArrayList<>();
	
//	private boolean resetsReduce = true;	// caching flag per operation
	
	final private CalleeCache<Method> traversingMethods 	= new CalleeCache<>();
//	* 
//	* Using {@link Set} of {@link Method}s to handle structurally false reseting-initiating, 
//	* such as subtract(...)-subtract_1(...)-subtract_2(...)-...
//	* 
//	* This set is synchronized.
//	final private Set<Method> initiatesElementalTraversals 	= 
//			Collections.synchronizedSet(new HashSet<>());

	final private Map<Pair<Cluster<Supplier<?>>, List<Object>>, Integer> 
	scs = new HashMap<>();
	
	
	
	/**
	 * Representing constant in AST
	 */
	private Boolean isConstant = null;
	
	/**
	 * scopeManager.getGlobalScope() returns null if some VOPConditions
	 * 	is the global scope and being initialized.
	 */
	private Boolean isGlobal = null;


	
	/**
	 * @param scopeManager - null is only allowed and ignored for constants
	 */
	public SystemElement(VODCondGen condGen) {
		this(null, condGen);
	}
	
	/**
	 * @param rtAddr - some run-time address. Null means the same as the one in the original AST.
	 * @param condGen - null is only allowed and ignored for constants
	 */
	public SystemElement(ASTAddressable rtAddr, VODCondGen condGen) {
		if (condGen == null) {
			if (testsNot(isConstant())) 
				throwNullArgumentException("VOP condition generator!");
			setGlobal();
			return;
		}
//		if (CondGen != null || CondGen == condGen) return;
		CondGen = condGen;
		
		if (rtAddr == null) {
			if (this instanceof ASTAddressable) rtAddr = (ASTAddressable) this;
			// isConstant() and isGlobal() may be not ready yet here for subclasses
//			else if (testsNot(isConstant()) && testsNot(isGlobal())) 
//				throwNullArgumentException("address");
		}
		runtimeAddress = rtAddr;
	}

	
	
	public Integer add(Supplier<?> supplier, Object... args) {
		return add(scs, supplier, args);
	}
	
	static private Integer add(
			Map<Pair<Cluster<Supplier<?>>, List<Object>>, Integer> callees, 
			Supplier<?> callee, Object... args) {
		if (callee == null) throwNullArgumentException("supplier");
		
		@SuppressWarnings({ "unchecked", "rawtypes" })
		final Pair<Cluster<Supplier<?>>, List<Object>> key = 
				new Pair<>(new SupplierCluster(callee), Elemental.toList(args));
		final Integer count = callees.get(key);
		return callees.put(key, count == null ? 1 : count + 1);
	}
	
	public Integer remove(Supplier<?> supplier, Object... args) {
		return remove(scs, supplier, args);
	}
	
	static private Integer remove(
			Map<Pair<Cluster<Supplier<?>>, List<Object>>, Integer> callees, Supplier<?> supplier, Object... args) {
		if (supplier == null) throwNullArgumentException("supplier");
		
		@SuppressWarnings({ "unchecked", "rawtypes" })
		final Pair<Cluster<Supplier<?>>, List<Object>> key = 
				new Pair<>(new SupplierCluster(supplier), Elemental.toList(args));
		final Integer count = callees.get(key);
		if (count == null) return null;
		if (count == 1) return callees.remove(key);
		return callees.put(key, count - 1);
	}
	
	public int contains(Supplier<?> supplier, Object... args) {
		return contains(scs, supplier, args);
	}
	
	static private int contains(
			Map<Pair<Cluster<Supplier<?>>, List<Object>>, Integer> callees, 
			Supplier<?> callee, Object... args) {
		if (callee == null) throwNullArgumentException("supplier");
		return Elemental.get(
				()-> callees.get(new Pair<>(new SupplierCluster<>(callee), 
						Elemental.toList(args))), 
				()-> 0, e-> -1);
	}
	
	public void clear() {
		scs.clear();
	}
	
	
	
	@Override
	final public Object clone() {
		return tests(isConstant())
				? this
				: cloneNonConstant();
	}
	
	@SuppressWarnings("unchecked")
	protected <T extends SystemElement> T cloneChangeAddressTo(ASTAddressable newRtAddr) {
		if (newRtAddr == null) throwNullArgumentException("runtime address");
		
		final SystemElement clone = (SystemElement) clone();
		clone.runtimeAddress = newRtAddr;
		return (T) clone;
	}
	
	protected Object cloneNonConstant() {
		try {
			// Calling {@link Object#clone()} default procedure first
			final SystemElement clone = (SystemElement) super.clone();
			clone.runtimeAddress = runtimeAddress;
			clone.isConstant = isConstant;
			clone.isGlobal = isGlobal;
			clone.setDirty();
			return clone;
			
		} catch (CloneNotSupportedException e) {
			return throwTodoException("unsupported clone!");
		}
	}
	
	

	@SafeVarargs
	static public <T> void consume(Consumer<T> con, Supplier<T> input, Consumer<Exception> conAlt, 
			Supplier<Boolean>... conjTesters) {
		Elemental.consume(con, input, conAlt, conjTesters);
	}
	
	public <T, E extends Exception> void consumeNonNull(
			final Consumer<T> con, final TrySupplier<T, E> inputSup, 
			@SuppressWarnings("unchecked") Supplier<Boolean>... conjTesters) throws E {
		Elemental.consumeNonNull(con, inputSup, conjTesters);
	}
	
	public <T> void consumeSkipNull(
			Consumer<T> con, Supplier<T> inputSup, 
			@SuppressWarnings("unchecked") Supplier<Boolean>... conjTesters) {
		Elemental.consumeSkipNull(con, inputSup, conjTesters);
	}
	
	public <T> void consumeSkipNullException(
			Consumer<T> con, Supplier<T> inputSup, 
			@SuppressWarnings("unchecked") Supplier<Boolean>... conjTesters) {
		guard(()-> Elemental.consumeSkipNullException(con, inputSup, conjTesters));
	}
	
	static public <T> boolean addSkipNull(
			Collection<T> col, Supplier<T> eleSup) 
			throws Exception {
		return Elemental.addSkipNull(col, eleSup);
	}
	
	static public <T> boolean addSkipException(Collection<T> col, T ele) {
		try {
			return Elemental.add(
					col, (Supplier<T>) ()-> ele, ASTUtil.DEFAULT_EXCEPTION);
			
		} catch (Exception e) {
			return throwInvalidityException("false default exception", e);
		}
	}
	
	@SafeVarargs
	static public <T> boolean addAllSkipNull(Collection<T> col, 
			Supplier<Collection<? extends T>> col2Sup, 
			Supplier<Boolean>... conjTesters) {
		return Elemental.addAllSkipNull(col, col2Sup, conjTesters);
	}
	
	@SuppressWarnings("unchecked")
	static public <T, E extends Exception> boolean addAllSkipNull(Collection<T> col, 
			TrySupplier<Collection<? extends T>, E> col2Sup) throws E {
		final List<E> nonSkips = new ArrayList<>();
		final boolean result = Elemental.addAllSkipNull(col, col2Sup.toSupplier(nonSkips));
		for (E e : nonSkips) {
			if (e instanceof NullPointerException) continue;
			throw e;
		}
		return result;
	}
	
	static public <T> boolean addAllSkipException(
			Collection<T> col, Supplier<Collection<? extends T>> col2Sup) {
		return Elemental.addAllSkipException(col, col2Sup);
	}
	
	static public <T, U, R> R apply(
			BiFunction<T, U, R> func, Supplier<T> input1, Supplier<U> input2, Function<Exception, R> returnAlt) {
		return Elemental.apply(func, input1, input2, returnAlt);
	}

	@SafeVarargs
	static public <T, R> R apply(
			Function<T, R> func, Supplier<T> input, Function<Exception, R> returnAlt, 
			Supplier<Boolean>... conjTesters) {
		return Elemental.apply(func, input, returnAlt, conjTesters);
	}
	
	@SafeVarargs
	static public <T, R, E extends Exception> R apply(
			TryFunction<T, R> func, Supplier<T> input, 
			TrySupplier<R, E> returnAltNull, TryFunction<Exception, R> returnAltExc, 
			Class<? extends Exception>... skips) {
		return Elemental.apply(func, input, returnAltNull, returnAltExc, skips);
	}
	
	static public String applySkipEmpty(
			Function<String, String> func, Supplier<String> inputSup) 
					throws Exception {
		return Elemental.applySkipEmpty(func, inputSup);
	}

	static public <T, R> R applySkipNull(
			Function<T, R> func, Supplier<T> inputSup) {
//			Function<T, R> func, Supplier<T> inputSup, Supplier<Boolean>... conjTesters) {
		return Elemental.applySkipNull(func, inputSup);
//		return Elemental.applySkipNull(func, inputSup, conjTesters);
//		return super.applySkipNull(func, inputSup, conjTesters);
	}
	
	public <T, R> R applySkipNull(
			Function<T, R> func, 
			Supplier<T> inputSup, Function<Exception, R> nnpeFunc, 
			@SuppressWarnings("unchecked") Supplier<Boolean>... conjTesters) {
		return Elemental.applySkipNull(func, inputSup, nnpeFunc, conjTesters);
//		return super.applySkipNull(func, inputSup, conjTesters);
	}
	
	@SafeVarargs
	static public <T, R> R applySkipNullThrow(
			TryFunction<T, R> func, Supplier<T> inputSup, Class<? extends Exception>... skips) 
					throws Exception {
		return Elemental.applySkipNull(func, inputSup, skips);
	}
	
	public void run(final Runnable r, 
			@SuppressWarnings("unchecked") Supplier<Boolean>... conjTesters) {
		Elemental.run(r, conjTesters);
	}
	
	public static void run(Runnable r, Consumer<Exception> alt) {
		get(()-> {r.run(); return null;}, e-> {alt.accept(e); return null;});
	}
	
	static public void runSkipNull(final Runnable r) {
		Elemental.runSkipNull(r);
	}
	
	static public void runSkipException(final Runnable r) {
		Elemental.runSkipException(r);
	}
	
	public static <T> T get(Supplier<T> sup, Supplier<T> nullAlt) {
		return Elemental.get(sup, nullAlt, null);
	}
	
	public static <T> T get(Supplier<T> sup, Function<Exception, T> alt) {
//		return super.get(sup, alt);
		return Elemental.get(sup, alt);
	}
	
	public static <T> T get(
			Supplier<T> sup, Supplier<T> nullAlt, Function<Exception, T> excAlt) {
		return Elemental.get(sup, nullAlt, excAlt);
	}
	
	static public <T> T getNonNull(Supplier<T> sup) {
		return Elemental.getNonNull(sup);
	}
	
	static public <T> T getNonException(Supplier<T> sup) {
		return Elemental.getNonException(sup);
	}
	
	static public <T> T getSkipNull(Supplier<T> sup) {
		return Elemental.getSkipNull(sup);
	}

	@SafeVarargs
	static public <T, E extends Exception> T getSkipNull(
			TrySupplier<T, E> sup, Function<E, T> execAlt, Class<? extends Exception>... skips) {
		return Elemental.getSkipNull(sup, execAlt, skips);
	}
	
	static public <T> T getSkipEmpty(Function<Collection<T>, T> func, Supplier<Collection<T>> sup) {
		return Elemental.getSkipEmpty(func, sup);
	}
	
	public <T> T getSkipException(Supplier<T> sup) {
//		return DebugElement.getSkipException(this, sup);
		return Elemental.getSkipException(sup);
	}
	
	public <T, E extends Exception> T getTry(TrySupplier<T, E> sup, Function<Exception, T> alt) {
		return Elemental.getTry(sup, alt);
	}
	
	public static <T, E extends Exception> T getThrow(
			TrySupplier<T, E> sup) throws E {
		return Elemental.getThrow(sup);
	}
	
	public static <T, E extends Exception> T getThrow(
			TrySupplier<T, E> sup, Supplier<T> nullAlt) throws E {
		return Elemental.getThrow(sup, nullAlt);
	}
	
	public static <T, E extends Exception> T getNullThrow(
			TrySupplier<T, E> sup, TrySupplier<T, E> nullAlt) throws E {
		return Elemental.getNullThrow(sup, nullAlt);
	}

	
	
	/**
	 * An instance method to return the static condition generator reference after instantiation
	 * since it's initiated during any construction of instance.
	 * 
	 * @return
	 */
	public VODCondGen getCondGen() {
		return CondGen;
//		return CondGen == null
//				? null
//				: debugGet(CondGen);
//				: CondGen.get();
	}
	

	
	final public void guard(Runnable runnable, Object... args) {
		guard(()-> {runnable.run(); return null;}, ()-> null, args);
	}
	
//	final public <T> T guard(Supplier<T> returnSupplier, Object... args) {
//		return guard(returnSupplier, null, args);
//	}
	
	final public <T> T guard(Supplier<T> returnSupplier, Method callee) {
		return guard(returnSupplier, ()-> null, callee);
	}
	
	final public <T> T guard(Supplier<T> returnSupplier, 
			Supplier<T> reenterSupplier, Object... args) {
		return guard(
				returnSupplier, 
				reenterSupplier,
				(Function<Exception, T>) null, 
				args);
//		return guard(
//				returnSupplier, 
//				altSupplier == null ? null : ()-> altSupplier.apply(null), 
//				altSupplier, 
//				args);
	}
	
	final public <T> T guard(Supplier<T> returnSupplier, 
			Supplier<T> reenterSupplier, Method callee) {
		try {
			return callee == null
					? guardThrow(returnSupplier, reenterSupplier, null)
					: guardThrow(returnSupplier, reenterSupplier, null, callee);
		} catch (Exception e) {
			return throwTodoException(e);
		}
	}
	
	final public <T> T guard(
			Supplier<T> returnSupplier, Supplier<T> reenterSupplier, 
			Function<Exception, T> excSupplier, Method callee) {
		try {
			return guardThrow(returnSupplier, reenterSupplier, excSupplier, callee);
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	
	final public <T> T guard(
			Supplier<T> returnSupplier, Supplier<T> reenterSupplier, 
			Function<Exception, T> excSupplier, Object... args) {
		return guard(this, returnSupplier, reenterSupplier, excSupplier, args);
	}
	
	static public <T> T guard(
			SystemElement caller, Supplier<T> callee, 
			Supplier<T> reenterSupplier, Function<Exception, T> excSupplier, Object... args) {
		return guard(caller, callee, reenterSupplier, 1, excSupplier, args);
	}
	
	static public <T> T guard(
			SystemElement caller, Supplier<T> callee, 
			Supplier<T> reenterSupplier, int reenterCount,
			Function<Exception, T> excSupplier, Object... args) {
		if (callee == null) throwNullArgumentException("callee");
		
		final Map<Pair<Cluster<Supplier<?>>, List<Object>>, Integer> callees = 
				caller == null ? INDEPENDENT_CALLEES : caller.scs;
		try {
			if (contains(callees, callee, args) == reenterCount) {
				// handling ReenterException implicitly
				return reenterSupplier == null
						? caller.throwReenterException(callee)
						: reenterSupplier.get();
			}
			
			add(callees, callee, args);
			T result = callee.get();
//			remove(callees, callee, args);	
			return result;

		} catch (ReenterException e) {
			// handling ReenterException explicitly
			return reenterSupplier == null
					? caller.throwReenterException(callee)
					: reenterSupplier.get();

		} catch (Exception e) {
			if (excSupplier == null) throw e;
			return excSupplier.apply(e);
		
		} finally {
			/* always removing, including ReenterException cases, 
			 * since it's a private operation 
			 */
			remove(callees, callee, args);	
		}
	}
	
	
	
	static final public boolean guardTests(Supplier<Boolean> tester) {
		return tests(guard(null, tester, ()-> null, e-> null));
	}
	
	
	
//	@SuppressWarnings("unchecked")
//	final public void guardThrow(TryRunnable runnable) throws Exception {
//		final List<Exception> nonSkips = new ArrayList<>();
//		guard(()-> {runnable.toRunnable(nonSkips).run(); return null;}, ()-> null);
//		if (!nonSkips.isEmpty()) throw nonSkips.get(0);
//	}
	
//	final public <T> T guardThrow(
//			Supplier<T> returnSupplier) throws ReenterException {
//		return guardThrow(returnSupplier, (Supplier<T>) null, null);
//	}
	
	/**
	 * @param <T>
	 * @param returnSupplier
	 * @param callee
	 * @return
	 * @throws Exception - must throw ReenterException if generated
	 */
	final public <T> T guardThrow(
			Supplier<T> returnSupplier, Method callee) 
					throws ReenterException {
		return guardThrow(returnSupplier, (Supplier<T>) null, null, callee);
	}
	
	final public <T> T guardThrow(
			Supplier<T> returnSupplier, Supplier<T> reenterSupplier, 
			Function<Exception, T> excSupplier, Method... callees) {
//		if (callees == null || callees.length == 0) 
//			throwNullArgumentException("useless guard without any callee");
		
		try {
			// native re-entering
			if (enters(callees)) 
				return throwReenterException(reenterSupplier, callees);
					
			enter(callees);
			final T returnObj = Elemental.getNonNullSupplier(returnSupplier);
//			final T returnObj = debugCallDepth(returnSupplier);
			leave(callees);
			return returnObj;
			
		} catch (Exception e) {
			assert e != null;
			// for foreign re-entering
			if (e instanceof ReenterException) 
				return throwReenterException(reenterSupplier, callees);
//				throwTodoException("truly inevitable reentering", e, callees);
			else {
				leave(callees);
				if (excSupplier != null) return excSupplier.apply(e);
			}
			throw e;
		}
	}
	
	final public <T, E extends Exception> T guardThrow(
			TrySupplier<T, E> returnSupplier, Method callee, Object... args) 
//			TrySupplier<T, E> returnSupplier, final List<Class<? extends Exception>> skips, Method callee, Object... args) 
			throws E {
		if (returnSupplier == null) throwNullArgumentException("supplier");
		
		final List<E> nonSkips = new ArrayList<>();
		@SuppressWarnings("unchecked")
		final Supplier<T> sup = returnSupplier.toSupplier(nonSkips);
		final T returnObj = callee == null
				? guard(sup, null, args)
				: guardThrow(sup, callee);
		if (!nonSkips.isEmpty()) throw nonSkips.get(0);
		return returnObj;
	}

	final public void guardSkipException(Runnable runnable, Method... callees) {
		guardSkipException(()-> {runnable.run(); return null;}, callees);
	}
	
	final public <T> T guardSkipException(Supplier<T> returnSupplier, Method... callees) {
		if (enters(callees)) return leave(null, callees);
		
		enter(callees);
		final T returnObj = Elemental.getSkipException(returnSupplier);
		leave(callees);
		return returnObj;
	}
	
	public void enter(Method callee) {
		if (callee == null) throwNullArgumentException("callee");
		traversingMethods.put(callee);
	}
	
	public void enter(Method... callees) {
		if (callees == null) throwNullArgumentException("callee");
		for (Method callee : callees) enter(callee);
	}
	
	public boolean enters() {
		return !traversingMethods.isEmpty();
	}
	
	public boolean enters(Method... callees) {
		final boolean entersAny = enters();
		if (callees == null) return entersAny;
		if (entersAny) for (Method callee : callees) 
			if (traversingMethods.contains(callee)) return true;
		return false;
	}
	
	public <T> T leave(Method callee) {
		if (callee == null) throwNullArgumentException("callee!");
//		if (!initiatesElementalTraversal(callee)) 
//			Debug.throwInvalidityException("false initiating callee");
		traversingMethods.remove(callee);
//		clear();
		return null;
	}
	
	public void leave(Method... callees) {
		if (callees == null) throwNullArgumentException("callee");
		for (Method callee : callees) leave(callee);
	}
	
	public <T> T leave(T result, Method... callees) {
		if (callees == null) leaveTotally();
		else leave(callees);
		return result;
	}
	
//	public <T> T leave(Method callee, Supplier<T> resultSupplier) {
//		if (resultSupplier == null) throwNullArgumentException("result supplier");
//		final T result = resultSupplier.get();
//		leave(callee);
//		return result;
//	}
	
	protected void leaveTotally() {
		traversingMethods.clear();;
		clear();
	}
	
	protected void leaveTotally(Method callee) {
		if (callee == null) throwNullArgumentException("callee!");
//		if (!initiatesElementalTraversal(callee)) 
//			Debug.throwInvalidityException("false initiating callee");
		traversingMethods.clear(callee);
		clear();
	}
	
	protected <T> T log(String message, Method... callees) {
		return log(null, message, callees);
	}

	protected <T> T log(String progress, String message, Method... callees) {
		if (callees != null) leave(callees);
		return getCondGen().log(progress, message);
	}
	
	
	
	final public boolean equals(Object obj) {
		if (obj == null) return false;
		if (this == obj) return true;
//		if (getClass() != obj.getClass()) return false;	NOT working for number-type-casting
		// ex. Int.equals(Real)
		
		try {
			SystemElement e2 = (SystemElement) obj;
			if (equalsToHashCode(e2)) return true;
			
			e2 = e2.reduce(METHOD_EQUALS);
//			eqList.clear();
			for (SystemElement e1 : eqList) if (e1 == e2) return true;
//			for (Element e1 : ieqList) if (e1 == e2) return false;
			
			SystemElement e1 = reduce(METHOD_EQUALS);
			assert e1 != null;
			if (e1.equalsToCache(e2)) return eqList.add(e2);
//			else return !ieqList.add(e2);
		} catch (NullPointerException | ClassCastException e) {
		} catch (Exception e) {
			throwTodoException(e);
		}
		return super.equals(obj);
	}
	
	public boolean equalsGlobal() {
		assert getCondGen() != null;
		return equals(getCondGen().getGlobalScope());
	}
	
	/**
	 * Distinguishing object equivalence checking from the (possibly) logically one.
	 * 
	 * @param e2
	 * @return
	 */
	protected boolean equalsObject(SystemElement e2) {
		return super.equals(e2);
	}
	
//	protected <T extends Element> boolean equalsToCache(T e2) {
	protected boolean equalsToCache(SystemElement se2) 
			throws ClassCastException, NullPointerException {
		return equalsObject(se2);
	}
	
	private boolean equalsToHashCode(SystemElement e2) {
		assert e2 != null && e2 != this && getClass() == e2.getClass();
		assert hashCode() != -1 && e2.hashCode() != -1;
		
		return hashCode() == e2.hashCode();
//		if (hashCode() != e2.hashCode()) return false;
//		return hashCodeOverflow == e2.hashCodeOverflow;
	}
	


	/**
	 * @return variable list for the hash-code polynomial.
	 */
	protected List<Integer> hashCodeVars() {
		return hashCodeObject();
	}
	
	final public List<Integer> hashCodeObject() {
		return Arrays.asList(super.hashCode());
	}
	
	final public int hashCode() {
		if (!isDirty()) return hashCode.hashCode();
//		assert hashCode == -1;
		assert hashCode == null;
		
		// consistent to equals(Element) semantics, but reducing n-ary Equality to much to unary ones
//		SystemElement r = reduce(METHOD_HASH_CODE);
//		if (r != this) return hashCode = r.hashCode();

		final int PRIME = 31;
		final List<Integer> hcvs = hashCodeVars();
		if (hcvs == null || hcvs.isEmpty()) throwTodoException("no hash code variables?");
		hashCode = BigInteger.ZERO;
		for (Integer hcv : hcvs) {
			if (hcv == null) throwTodoException("null hash code-let");
			hashCode = hashCode.multiply(BigInteger.valueOf(PRIME))
					.add(BigInteger.valueOf(Math.abs(hcv)));
//			final int hashCodePre = hashCode;
//			hashCode += PRIME * Math.abs(hcv);
//			if (hashCode < hashCodePre) {
//				hashCodeOverflow++;
//				if (hashCodeOverflow == Integer.MIN_VALUE) throwTodoException("hashCode Overflow!");
//			}
		}
		return hashCode.hashCode();
	}
	
	
	
	abstract protected Boolean cacheConstant();
	
	protected Boolean setConstant(Boolean isConst) {
		/* isConstant -> !isConstant: caused by re-assigned
		 * !isConstant -> isConstant: non-sense
		 */
		if (isConstant != null && isConst != null && !isConstant && isConst)	
			throwTodoException("contradictive constant setting");	
		return isConstant = isConst;
	}
	
	/**
	 * @param <T>
	 * @return valid value <em>only if</em> {@link #isConstant()} returns true.
	 * @throws ASTException 
	 * @throws UncertainException 
	 * 	since <code>super.toConstantIf()</code> doesn't pass exceptions 
	 * 	generated from sub-classes.
	 */
	protected <T extends SystemElement> T toConstantIf() 
			throws ASTException, UncertainException {
		return null;
	}

	/**
	 * @return null if this is neither constant nor sure to be constant.
	 */
	@SuppressWarnings({ "unchecked" })
	final public <T extends SystemElement> T toConstant() 
			throws ASTException, UncertainException {
		try {
			return tests(isConstant()) 
					? guard(()-> toConstantIf(),
							()-> (T) this,
							METHOD_TO_CONSTANT)
					: null;
					
		} catch (ASTException | UncertainException e) {
			throw e;
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	
	/**
	 * @return true if it's conditionally or unconditionally constant (to its context)
	 */
	final public Boolean isConstant() {
		if (isConstant != null) return isConstant;
		try {
			return isConstant = cacheConstant();
//			return isConstant = debugCallDepth(()-> cacheConstant());
			
		} catch (Exception e) {
			return throwTodoException(e);
		}
	}
	
	
	
	final public Boolean isGlobal() {
		if (isGlobal != null) return isGlobal;
		
		setGlobal(cacheGlobal());
		return isGlobal;
	}

	/**
	 * isConstant() -> isGlobal();
	 * isGlobal() -/-> isConstant().
	 * @return
	 */
	protected Boolean cacheGlobal() {
		if (CondGen == null || CondGen.equalsGlobal() || tests(isConstant())) return true;
		return null;
	}
	
	public void setGlobal() {
		setGlobal(true);
	}
	
	public void setGlobal(Boolean isGlobal) {
		if (this.isGlobal != null && isGlobal != null) {
			if (!this.isGlobal.equals(isGlobal)) throwTodoException("inconsistent global-ness");
		}
		this.isGlobal = isGlobal;
	}
	

	
	protected boolean isDirty() {
		return hashCode == null;
//		return hashCode == -1;
	}
	
	/**
	 * Resetting children content and properties, such as hash code.
	 * 
	 * AST reset may result in element destructions. Therefore element rest doesn't always
	 * mean AST reset.
	 */
	protected void setDirty() {
		hashCode = null;
//		hashCode = -1;
//		hashCodeOverflow = 0;
		isConstant = null;
//		resetsReduce = true;	// un-setting reduce as early as possible?
//		reduce();		// reduce at logic (entry) operation time
		leaveTotally();
	}

	protected void setNotDirty() {
		hashCode();	//re-computing hash code anyway
	}
	
	
	
	public ASTAddressable cacheRuntimeAddress() {
//		if (runtimeAddress == null)
//			if (testsNot(isConstant()) && testsNot(isGlobal())) 
//				throwNullArgumentException("address");
		return runtimeAddress;
	}
	
	/**
	 * A mutable convergent reduction to this element.
	 * 
	 * @param caller
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public final <T extends SystemElement> T reduce(Method caller) {
		if (!isDirty() || enters(caller)) return (T) this;
		if (tests(isConstant())) try {
			return setReduce(toConstantIf());
		} catch (ASTException | UncertainException e) {
			return (T) this;
		}

		enter(caller);	// reduceOnce() may call some element's reduce()
		T re1 = (T) this, re2 = reduceOnce();
		while (re2 != re1) {
			re1 = re2;
			re2 = reduceOnce();
		}
		leave(caller);
		return setReduce(re2);
	}

	/**
	 * A mutable one-time reduction to this element.
	 * @return
	 */
	@SuppressWarnings("unchecked")
	protected <T extends SystemElement> T reduceOnce() {return (T) this;}
	
	private <T extends SystemElement> T setReduce(T re) {
		if (re == null) throwInvalidityException("reduce to null");
		
		if (re != this) setDirty();
//		resetsReduce = false;
		return re;
	}
	
	
	
	static public boolean tests(final Boolean tester) {
		return Elemental.tests(tester);
	}
	
	static public boolean tests(final Supplier<Boolean> tester) {
		return Elemental.tests(tester);
	}
	
	static public boolean testsNot(final Boolean tester) {
		return Elemental.testsNot(tester);
	}
	
	static public boolean testsNot(final Supplier<Boolean> tester) {
		return Elemental.testsNot(tester);
	}
	
	static public <T> boolean testsSkipNull(Function<T, Boolean> tester, Supplier<T> tSup) {
		return Elemental.testsSkipNull(tester, tSup);
	}
	
	static public boolean testsNonNull(Supplier<Boolean> tester) {
		return Elemental.testsNonNull(tester);
	}
	
	@SafeVarargs
	static public Boolean testsAnySkipNull(Supplier<Boolean>... disjTesters) {
		return Elemental.testsAnySkipNull(disjTesters);
	}
	
	@SafeVarargs
	static public Boolean testsAnySkipNullException(Supplier<Boolean>... disjTesters) {
		return Elemental.testsAnySkipNullException(disjTesters);
	}
	
	@SafeVarargs
	static public Boolean testsFirst(Supplier<Boolean>... disjTesters) {
		return Elemental.testsFirst(disjTesters);
	}
	
	@SafeVarargs
	static public Boolean testsSkipNull(Supplier<Boolean>... conjTesters) {
		return Elemental.testsSkipNull(conjTesters);
	}
		
	public <T> T testsSkipNull(Boolean tester, Supplier<T> trueResult, Supplier<T> falseResult) {
//		return super.testsSkipNull(tester, trueResult, falseResult);
		return Elemental.testsSkipNull(tester, trueResult, falseResult);
	}

	
	
	public <T, E extends Exception> T trySkipException(
			final List<Class<? extends Exception>> skips, 
			@SuppressWarnings("unchecked") TrySupplier<T, E>... tries) 
					throws Exception {
//		return trySkipException(true, skips, Arrays.asList(tries), null);
		return trySkipException(null, skips, tries);
	}
	
	public <T, E extends Exception> T trySkipException(
			final Method callee, final List<Class<? extends Exception>> skips, 
			@SuppressWarnings("unchecked") final TrySupplier<T, E>... tries) 
					throws Exception {
		return trySkipException(false, skips, Arrays.asList(tries), callee);
	}
	
	public <T> T trySkipNullException(final Class<? extends Exception>[] skips, 
			@SuppressWarnings("unchecked") final Supplier<T>... tries) 
			throws Exception {
		return trySkipNullException(Arrays.asList(skips), Arrays.asList(tries), null);
	}
	
	public <T> T trySkipNullException(
			final Method callee, final Class<? extends Exception>[] skips, 
			@SuppressWarnings("unchecked") final Supplier<T>... tries) 
					throws Exception {
		return trySkipNullException(Arrays.asList(skips), Arrays.asList(tries), callee);
	}
	
	public <T, E extends Exception> T trySkipNullException(
			List<Class<? extends Exception>> skips, final List<Supplier<T>> tries, Method callee) 
					throws Exception {
		final List<TrySupplier<T, E>> tries2 = new ArrayList<>();
		for (Supplier<T> try1 : tries) tries2.add(()-> {try {
			return try1.get();
		} catch (Exception e) {throw e;}});
		return trySkipException(true, skips, tries2, callee);
	}
	
	/**
	 * @param <T>
	 * @param skipsNull
	 * @param skips - what listed in skips causing returning null
	 * @param tries
	 * @param callee
	 * @return
	 * @throws Exception
	 */
	private <T, E extends Exception> T trySkipException(
			final boolean skipsNull, List<Class<? extends Exception>> skips, 
			final List<TrySupplier<T, E>> tries, Method callee) 
					throws Exception {
		if (tries == null) throwNullArgumentException("supplier");
		final int trySize = tries.size();
		if (trySize == 0) throwNullArgumentException("supplier");
		
		final List<TrySupplier<T, E>> subTries = trySize > 1 ? 
				tries.subList(1, trySize) : null;
		try {
			final T result = guardThrow(tries.get(0), callee);
			return skipsNull && result == null && subTries != null
					? trySkipException(skipsNull, skips, subTries, callee) 
					: result;
					
		} catch (Exception e) {
			// including testing NullPointerException
			if (skips != null) 
				for (Class<? extends Exception> skip : skips)
					if (skip.isInstance(e)) return subTries == null
					? null	// skips exceptions
					: trySkipException(skipsNull, skips, subTries, callee);
			
			// at last NullPointerException
			if (skipsNull && e instanceof NullPointerException) return null;
			throw e;
		}
	}
	
	
	
	public static boolean isUncertainException(Exception e) {
		return e instanceof UncertainException;
	}
	
	public static <T> T throwFunctionalException() 
			throws UnsupportedOperationException {
		return throwTodoException("loop iterator must ONLY be an array index");
	}
	
	public static <T> T throwInvalidityException(String message) {
		return DebugElement.throwInvalidityException(message);
	}
	
	public <T> T throwInvalidityException(Method callee, Exception e, String message) {
		leave(callee);
		return throwInvalidityException(message, e);
	}
	
	public static <T> T throwNullArgumentException(String arg) {
		return DebugElement.throwNullArgumentException(arg);
//		return null;
	}
	
	public <T> T throwReductionException(Method callee) {
		leave(callee);
		return super.throwReductionException();
	}
	
	public <T> T throwReenterException(Method... callees) 
			throws ReenterException {
		throw new ReenterException(this, callees);
	}
	
	public <T> T throwReenterException(Supplier<T> callee) 
			throws ReenterException {
		throw new ReenterException(this, callee);
	}
	
	public <T> T throwReenterException(Supplier<T> reenterSupplier, Method... callees) 
			throws ReenterException {
		if (reenterSupplier != null) {
			// only un-handled ReenterException doesn't leave(callees)
			leave(callees);
			return reenterSupplier.get();
		}
		throw new ReenterException(this, callees);
	}
	
	public static <T> T throwTodoException(String message) 
			throws UnsupportedOperationException {
		return DebugElement.throwTodoException(message);
	}

	public static <T> T throwTodoException(Exception e) {
		return DebugElement.throwTodoException(e);
	}
	
	public <T> T throwTodoException(Exception e, Method callee) {
		return throwTodoException(null, e, callee);
	}
	
	public <T> T throwTodoException(String message, Exception e, Method... callees) {
		leave(callees);
		return super.throwTodoException(message, e);
	}
	
	public <T> T throwUncertainException(Method callee) 
			throws UncertainException {
		return throwUncertainException(null, callee);
	}
	
	public <T> T throwUncertainException(String message, Method... callees) 
			throws UncertainException {
		return throwUncertainException(
				message, 
				null, 
				this, 
				callees);
	}
	
	public <T> T throwUncertainException(
			String message, Exception source, SystemElement caller, Method... callees) 
			throws UncertainException {
		leave(callees);
		try {
			throwHaltableException(
					new UncertainException(message, source, caller, callees));
		} catch (UncertainException e1) {
			throw e1;
		} catch (Exception e1) {
		}
		return null;
	}
	
	public static <T> T throwUncertainPlaceholderException(
			String message, Assignable<?> asn) 
					throws UncertainPlaceholderException {
		return throwUncertainPlaceholderException(message, null, asn);
	}
	
	public static <T> T throwUncertainPlaceholderException(String message, 
			Exception source, Assignable<?> asn, Method... callees) 
			throws UncertainPlaceholderException {
		throwHaltableException(
				new UncertainPlaceholderException(message, source, asn, callees));
		return null;
	}
	
	public <T> T throwUnhandledException(Exception source, Method... callees) {
		leave(callees);
		return super.throwUnhandledException(source);
	}
	
	public static <T> T throwUnsupportedNegation() 
			throws UnsupportedOperationException {
		return throwUnsupportedOperationException("unsupported negation");
	}
	
	public static <T> T throwUnsupportedOperationException(String message) 
			throws UnsupportedOperationException {
		throw new UnsupportedOperationException(message);
	}
	
}