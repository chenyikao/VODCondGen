/**
 * 
 */
package ompca.vodcg;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import java.util.function.Supplier;

import ompca.Elemental;
import ompca.Elemental.TrySupplier;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class DebugElement extends ompca.DebugElement {

//	public <T> T get(Supplier<T> sup) {
//		return get(sup, null);
//	}
	
//	public static <T> T get(Supplier<T> sup, Function<Exception, T> alt) {
//		try {
//			return debugCallDepth((Supplier<T>) ()-> 
//			Elemental.get(sup, alt));
//			
//		} catch (Exception e) {
//			if (alt == null) throwNullArgumentException("alternative");
//			return alt.apply(e);
//		}
//	}
	
//	static public <T> T get(DebugElement caller, Supplier<T> sup, Function<Exception, T> alt) {
//	return debugCallDepth(caller, ()-> Elemental.get(sup, alt));
//}

//static public <T> T getNonNull(Supplier<T> sup) {
//	return debugCallDepth((Supplier<T>)
//			()-> Elemental.getNonNull(sup));
//}

	public <T> T getNonNull(Supplier<T> sup, DebugElement caller) 
			throws Exception {
		return debugCallDepth(
				DEFAULT_DEPTH, 
				(SystemElement) caller, 
				()-> Elemental.getNonNull(sup));
	}
	
	static public <T> T getSkipNull(Supplier<T> sup) throws Exception {
		return debugCallDepth(null, ()-> Elemental.getSkipNull(sup));
	}
	
	static public <T> T getSkipNull(SystemElement caller, Supplier<T> sup) 
			throws Exception {
		return debugCallDepth(caller, ()-> Elemental.getSkipNull(sup));
	}
	
	static public <T> T getSkipException(SystemElement caller, Supplier<T> sup) {
		return debugCallDepth(caller, ()-> Elemental.getSkipException(sup));
	}
	
//	public <T, R> R applySkipNull(
//	Function<T, R> func, Supplier<T> inputSup, @SuppressWarnings("unchecked") Supplier<Boolean>... conjTesters) 
//			throws Exception {
//return debugCallDepth((Supplier<R>)
//		()-> Elemental.applySkipNull(func, inputSup, conjTesters));
//}

//public <T> void consumeSkipNull(
//	Consumer<T> con, Supplier<T> inputSup, 
//	@SuppressWarnings("unchecked") Supplier<Boolean>... conjTesters) 
//			throws Exception {
//debugCallDepth(()-> 
//Elemental.consumeSkipNull(con, inputSup, conjTesters));
//}



	public <T> T testsSkipNull(
			Boolean tester, Supplier<T> trueResult, Supplier<T> falseResult) {
		return debugCallDepth((Supplier<T>) ()-> 
		Elemental.testsSkipNull(tester, trueResult, falseResult));
	}
	
	
	
	public <T> T debugCallDepth(Supplier<T> call, Object... args) {
		return debugCallDepth((SystemElement) this, call, args);
	}
	
	public static <T> T debugCallDepth(
			SystemElement caller, Supplier<T> callee, Object... args) {
		return debugCallDepth(DEFAULT_DEPTH, caller, callee, args);
	}
	
	/**
	 * Debugging handles only stack overflow exceptions and throws others.
	 * 
	 * @param <T>
	 * @param depth is <em>not</em> precise since its counting may be interrupted by exception throwing
	 * @param caller
	 * @param callee
	 * @param args
	 * @return
	 */
	public static <T> T debugCallDepth(
			int depth, DebugElement caller, Supplier<T> callee, Object... args) {
		return caller == null || caller instanceof SystemElement
				? SystemElement.guard(
				(SystemElement) caller, callee, ()-> throwStackOverflowException(), depth, null, args)
				: throwTodoException("unsupported element type");
	}
	
	@SuppressWarnings("unchecked")
	public static <T, E extends Exception> T debugCallDepth(
			int depth, SystemElement caller, TrySupplier<T, E> callee, Object... args) 
					throws E {
		final List<E> nonSkips = new ArrayList<>();
		final T result = debugCallDepth(
				depth, caller, callee.toSupplier(nonSkips), args);
		if (!nonSkips.isEmpty()) throw nonSkips.get(0);
		return result;
	}
	
	public <T> T debugCallDepth(int count, Supplier<T> call, Object... args) {
		return debugCallDepth(count, (SystemElement) this, call, args);
	}
	
	public <T, E extends Exception> T debugCallDepth(
			int count, TrySupplier<T, E> call, Object... args) 
			throws E {
		return debugCallDepth(count, (SystemElement) this, call, args);
	}
	
	@SuppressWarnings("unchecked")
	public <T, E extends Exception> T debugCallDepthThrow(
			TrySupplier<T, E> call, Object... args) throws E {
		final List<E> nonSkips = new ArrayList<>();
		final T result = debugCallDepth(
				(SystemElement) this, 
				call.toSupplier(nonSkips), 
				args);
		if (!nonSkips.isEmpty()) throw nonSkips.get(0);
		return result;
	}
	
	public <T, R> R debugApply(
			Function<T, R> func, Supplier<T> input, Function<Exception, R> returnAlt, 
			@SuppressWarnings("unchecked") Supplier<Boolean>... conjTesters) {
		return debugCallDepth((SystemElement) this,
				(Supplier<R>) ()-> Elemental.apply(func, input, returnAlt, conjTesters));
	}

	public void debugRun(Runnable call, Object... args) {
		debugRun((SystemElement) this, call, args);
	}
	
	public static void debugRun(SystemElement caller, Runnable call, Object... args) {
		if (call == null) throwNullArgumentException("call");
		debugCallDepth(caller, ()-> {call.run(); return null;}, args);
	}
	
	public <T> T debugGet(Supplier<T> sup) {
		return debugCallDepth((SystemElement) this,
				(Supplier<T>) ()-> Elemental.getNonNullSupplier(sup));
	}
	
	public <T> T debugGet(int depth, Supplier<T> sup) {
		return debugCallDepth(depth, (SystemElement) this,
				(Supplier<T>) ()-> Elemental.getNonNullSupplier(sup));
	}
	
	public static <T> T debugGet(SystemElement caller, Supplier<T> sup, Object... args) {
		return debugCallDepth(caller, (Supplier<T>) ()-> Elemental.getNonNullSupplier(sup), args);
	}
	
	public <T> T debugGet(
			Supplier<T> sup, Function<Exception, T> alt) {
		return debugCallDepth((SystemElement) this,
				(Supplier<T>) ()-> Elemental.get(sup, alt));
	}
	
	public <T> T debugGet(
			Supplier<T> sup, Supplier<T> nullAlt) {
		return debugGet(sup, nullAlt, null);
	}
	
	public <T> T debugGet(
			Supplier<T> sup, Supplier<T> nullAlt, Function<Exception, T> excAlt) {
		return debugCallDepth((Supplier<T>) ()-> Elemental.get(sup, nullAlt, excAlt));
	}

	public <T> T debugGetNonNull(Supplier<T> sup) {
		return debugCallDepth((SystemElement) this,
				(Supplier<T>) ()-> Elemental.getNonNull(sup));
	}
	
	static public <T> T debugGetNonNull(SystemElement caller, Supplier<T> sup, Object... args) {
		return debugCallDepth(caller, (Supplier<T>) ()-> Elemental.getNonNull(sup), args);
	}
	
	public <T> T debugGetSkipNull(Supplier<T> sup) {
		return debugCallDepth((SystemElement) this,
				(Supplier<T>) ()-> Elemental.getSkipNull(sup));
	}
	
	public <T, E extends Exception> T debugGetThrow(
			TrySupplier<T, E> sup, Supplier<T> nullAlt) throws E {
		return debugCallDepthThrow(()-> Elemental.getThrow(sup, nullAlt));
	}
	
	public boolean debugTests(Supplier<Boolean> target) {
		return debugCallDepth((SystemElement) this,
				()-> Elemental.tests(target));
	}
	
}