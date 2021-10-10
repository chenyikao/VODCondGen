/**
 * 
 */
package ompca.vodcg.condition.version;

import java.util.NoSuchElementException;

import ompca.vodcg.condition.Referenceable;

/**
 * @author Kao, Chen-yi
 *
 */
public class NoSuchVersionException extends NoSuchElementException {

	private static final long serialVersionUID = -8897548649156317809L;

	
	
	private ThreadRoleMatchable role1 = null;
	private ThreadRoleMatchable role2 = null;
	
	public <Subject extends Referenceable> NoSuchVersionException(
			final VersionEnumerable<Subject> venum, String message, Exception cause) {
		super(message);
	}
	
	public <Subject extends Referenceable> NoSuchVersionException(
			final VersionEnumerable<Subject> venum, final ThreadRoleMatchable role1, final ThreadRoleMatchable role2) {
		this(venum, "unmatched roles: " + role1 + " and " + role2, null);
		this.role1 = role1;
		this.role2 = role2;
	}
	
	public boolean involvesRoles() {
		return role1 != null && role2 != null;
	}
	
}