/**
 * 
 */
package ompca.vodcg.condition.version;

import java.util.function.Supplier;

import ompca.vodcg.condition.Proposition;
import ompca.vodcg.condition.Referenceable;

/**
 * @author Kao, Chen-yi
 *
 */
public class RaceVersion<Subject extends Referenceable> extends Version<Subject> {

	private Supplier<Proposition> race = null;
	
	protected RaceVersion(VersionEnumerable<Subject> address, FunctionallableRole role, Supplier<Proposition> race) 
			throws NoSuchVersionException {
		super(address, role);

		if (race == null) throwNullArgumentException("race proposition");
		this.race = race;
	}
	
	/**
	 * @return non-null
	 */
	public Supplier<Proposition> getRaceAssertion() {
		assert race != null;
		return race;
	}
	
	@Override
	public boolean derives(ThreadRoleMatchable matchable2) {
		return true;
	}

	@Override
	public Proposition toProposition() {
		return getNonNull(getRaceAssertion()).andSkipNull(super.toProposition());
	}
	
}