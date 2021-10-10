package ompca.vodcg.condition.data;

import ompca.condition.Type;
import ompca.vodcg.VODCondGen;

/**
 * A platform means a simulated programming language (like C/C++) environment.
 * 
 * A platform type may include some numeric sub-types, i.e., int or float, etc.
 * But not all sub-types, i.e., char or pointer, have their positive or negative infinities defined.
 * 
 * @author Kao, Chen-yi
 *
 */
public interface PlatformType extends Type {

	public Number<?> getPositiveInfinity();
	public Number<?> getNegativeInfinity();
	
	default public boolean isCastableTo(PlatformType type2) {
		return this == type2;
	}
	
	default public boolean isPlatformBounded() {
		return VODCondGen.isBounded(this);
	}
	
}