/**
 * 
 */
package ompca.vodcg.condition;

/**
 * @author Kao, Chen-yi
 *
 */
public enum InductiveType {
	Pre,
	Closure,
	Post;
	
	public boolean isNonClosure() {
		return equals(Pre) || equals(Post);
	}
	
}