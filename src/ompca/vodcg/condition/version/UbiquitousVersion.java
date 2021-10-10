/**
 * 
 */
package ompca.vodcg.condition.version;

import ompca.vodcg.condition.Referenceable;

/**
 * A self completed version independent to subversion's. That means every subversion
 * level can be an independent level of versioning if each subversion is a ubiquitous one.
 * 
 * Self-complete-ness doesn't guarantee functional mapping.
 *  
 * @author Kao, Chen-yi
 *
 */
public interface UbiquitousVersion<Subject extends Referenceable> {
//extends AppendableVersion<Subject> {

//	/**
//	 * Doing nothing since this is supposed NOT a re-writable version.
//	 * 
//	 * @see ompca.condition.version.Version#append(ompca.condition.version.Version)
//	 */
//	@SuppressWarnings("unchecked")
//	default public Version<Subject> append(Version<Subject> subVer) {
//		return (Version<Subject>) this;
//	}

	public void checkUbiquitous();
	
	/**
	 * @param <E> - Allowing, for example, PathVariable <em>super</em> 
	 * 	FunctionalPathVariable makes UbiquitousVersion<FunctionalPathVariable> 
	 * 	reversion-able at all Assignable<PathVariable>'s.
	 * @param enumer
	 * @return
	 * @throws UnsupportedOperationException
	 */
	public <E extends VersionEnumerable<? super Subject>> 
	EnumeratedVersion<Subject, E> enumerate(E enumer)
	throws UnsupportedOperationException;
	
}