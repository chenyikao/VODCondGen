package ompca.vodcg;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;

import ompca.CallCache;
import ompca.DebugElement;
import ompca.Elemental;
import ompca.Pair;
import ompca.SupplierCluster;

/**
 * For preceding conditional statements (testers) in which 
 * NullPointerException (break) is NOT allowed.
 *  
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class ExceptionSkippingTesters<T, R> implements Elemental {

	/**
	 * Object.hashCode() doesn't trigger ExceptionSkippingTesters
	 */
	static private final CallCache<Object, SupplierCluster<?>> 
	TESTER_CACHE 			= new CallCache<>();
	
	final private Set<Class<Exception>> ets 			= new HashSet<>();
	final private List<Pair<T, Supplier<R>>> testers 	= new ArrayList<>();
//	final private List<Function<T,R>> 	testers = new ArrayList<>();
//	final private List<T> 				args 	= new ArrayList<>();
	
	private T defaultCaller = null;
	
	public ExceptionSkippingTesters(T caller, Class<Exception>[] exceptions) {
		this(exceptions);
		
		if (caller == null) DebugElement.throwNullArgumentException("caller");
		this.defaultCaller = caller;
	}
	
	public ExceptionSkippingTesters(Class<Exception>[] exceptions) {
		if (exceptions != null) ets.addAll(Arrays.asList(exceptions));
	}
	


	public boolean add(Supplier<R> tester) {
		return testers.add(new Pair<>(null, tester));
	}
	
	public boolean add(T caller, Supplier<R> tester) {
		return testers.add(new Pair<>(caller, tester));
	}
	
//	public boolean add(Function<T,V> tester, T arg) {
//		return args.add(arg) && testers.add(tester);
//	}



//	/**
//	 * Predictive guard for avoiding stack overflow errors/exceptions.
//	 * 
//	 * @param testers
//	 * @return
//	 */
//	public static boolean initiatesTesting(Supplier<?>[] testers) {
//		if (testers == null || testers.length == 0) return false;
//		
////		final Set<Cluster<?>> testerGroup = TESTER_CACHE.get(obj);
////		if (testerGroup == null) return false;
//		
//		for (Supplier<?> tester : testers) 
//			if (TESTER_CACHE.contains(tester)) return true;
//		return false;
//	}
	
	
	
//	public static boolean initiateTesting(Supplier<?>[] testers) {
//		if (testers == null || testers.length == 0) return false;
//		
//		Set<Cluster<?>> testerGroup = TESTER_CACHE.get(obj);
//		if (testerGroup == null) {
//			testerGroup = Collections.synchronizedSet(new HashSet<>());
//			TESTER_CACHE.put(obj, testerGroup);
//		}
//		
//		boolean result = false;
//		for (Supplier<?> tester : testers) 
//			result |= testerGroup.add(new SupplierCluster(tester));
//		return result;
//		return TESTER_CACHE.addAll(Arrays.asList(testers));
//	}
	
	
	
//	public static boolean resetTesting(Supplier<?>[] testers) {
//		if (testers == null || testers.length == 0) return false;
//		
//		final Set<Cluster<?>> testerGroup = TESTER_CACHE.get(obj);
//		if (testerGroup == null) return false;
//		
//		boolean result = false;
//		for (Supplier<?> tester : testers) 
//			result |= testerGroup.remove(new SupplierCluster(tester));
//		return result;
//		return TESTER_CACHE.removeAll(Arrays.asList(testers));
//	}
	
	
	
	/**
	 * Skipping intermediate null Boolean cases.
	 * 
	 * @param testers
	 * @return
	 */
	@SafeVarargs
	static public <T, R> R testSkipNullException(
			T caller, Supplier<R>... testers) {
		return test(caller, JavaUtil.NULL_POINTER_EXCEPTION_CLASS, testers);
	}
	
	@SafeVarargs
	static public <T, R> R testSkipNullClassCastException(
			T caller, Supplier<R>... testers) {
		return test(caller, JavaUtil.NULL_CLASS_CAST_EXCEPTION_CLASS, testers);
	}
	
	@SafeVarargs
	static public <T, R> R test(
			T caller, Class<Exception>[] exs, Supplier<R>... testers) {
		if (testers == null) return null;

		ExceptionSkippingTesters<T, R> ests = new ExceptionSkippingTesters<>(exs);
		for (Supplier<R> tester : Arrays.asList(testers)) ests.add(tester); 
		
		return ests.test(caller);
	}
	
	
	
	public R test() {
		return test(defaultCaller);
	}
	
	public R test(T defaultCaller) {
		if (defaultCaller == null) defaultCaller = this.defaultCaller;
		
		R result = null;
		tester: for (Pair<T, Supplier<R>> tester : testers) {
			T caller = tester.getPeer1();
			if (caller == null) caller = defaultCaller;
			if (caller == null) DebugElement.throwNullArgumentException("caller");
			
			Supplier<R> callee = tester.getPeer2();
			SupplierCluster<?> cc = new SupplierCluster<>(callee);
			try {
				if (!TESTER_CACHE.contains(caller, cc)) {
					TESTER_CACHE.put(caller, cc);
					result = callee.get();
//					result = Debug.debugCallDepth(300, tester);
				}
			} catch (Exception e) {
				for (Class<Exception> ec : ets) 
					if (ec.isInstance(e)) continue tester;
				DebugElement.throwUnhandledException(e);
			} finally {
//				if (!TESTER_CACHE.contains(caller, cc)) 
//					Debug.throwTodoException("asynchronous put-remove?");
				TESTER_CACHE.remove(caller, cc);
			}
			
			if (result != null) break;	// 'truly false' is recognized
		}
		return result;
	}
	
}