/**
 * 
 */
package ompca.vodcg.condition.version;

import ompca.Elemental.TrySupplier;
import ompca.vodcg.condition.Referenceable;

/**
 * @author Kao, Chen-yi
 *
 */
public interface AppendableVersion<Subject extends Referenceable> {

	public Version<Subject> append(TrySupplier<Version<Subject>, NoSuchVersionException> subVer);
	public Version<Subject> appendConstantCounting();
	
}