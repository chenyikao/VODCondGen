/**
 * 
 */
package ompca.vodcg.condition;

import ompca.Emptable;

/**
 * @author Kao, Chen-yi
 *
 */
public interface SideEffectElement extends Emptable {
	
	default boolean isGuard() {
		return false;
	}
	
	default boolean suitsSideEffect() {
		return true;
	}

}