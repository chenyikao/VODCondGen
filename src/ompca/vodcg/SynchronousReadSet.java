/**
 * 
 */
package ompca.vodcg;

import java.util.ConcurrentModificationException;
import java.util.Set;
import java.util.function.Consumer;

/**
 * @author Kao, Chen-yi
 *
 */
public class SynchronousReadSet<T> {

	private String name;
	private Set<T> kernel;
	
	@SuppressWarnings("deprecation")
	public SynchronousReadSet(Set<T> kernel, String name) {
		if (kernel == null) DebugElement.throwNullArgumentException("kernel set");
		this.name = name == null ? "" : name;
		this.kernel = kernel;
	}
	

	
	@SuppressWarnings("deprecation")
	public void forEach(final Consumer<T> elementConsumer, final VODCondGen cg,
			@SuppressWarnings("unchecked") final Class<Exception>... skips) {
		if (elementConsumer == null) DebugElement.throwNullArgumentException("element consumer");
		
		while (true) try {
			Eles: for (T ele : kernel) try {
				elementConsumer.accept(ele);
			} catch (Exception e) {
				if (skips != null) for (Class<Exception> skip : skips) 
					if (skip != null && skip.isInstance(e)) continue Eles;
				throw e;
			}
			break;
		} catch (ConcurrentModificationException e) {
			if (cg != null) cg.log(null, name + " reiterated by " + e);
			continue;
		}
	}
	
}