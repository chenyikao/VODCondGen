/**
 * 
 */
package ompca.vodcg.condition.version;

import ompca.vodcg.condition.PathVariablePlaceholder;
import ompca.vodcg.condition.Referenceable;

/**
 * The initial un-rewritten version. All {@link PathVariablePlaceholder}'s 
 * (l-value references of {@code var}) SHOULD share this version for its universal.
 * 
 * Universal version's scope is the one of its referring (subject) variable.
 *
 * TODO? pre-cached function scope for some function parameter var
 * 
 * @author Kao, Chen-yi
 *
 */
public class UniversalVersion<Subject extends Referenceable> 
extends Version<Subject> implements UbiquitousVersion<Subject> {

	/**
	 * @param subject
	 * @throws NoSuchVersionException 
	 */
	public UniversalVersion(Subject subject) throws NoSuchVersionException {
		super(subject, ThreadRole.MASTER);
	}

	public UniversalVersion(Subject subject, Boolean isGlobal) throws NoSuchVersionException {
		super(subject, ThreadRole.MASTER, isGlobal);
	}
	
	private UniversalVersion(VersionEnumerable<Subject> ve) throws NoSuchVersionException {
		super(ve, ThreadRole.MASTER);
	}
	
	public static <Sbj extends Referenceable> Version<Sbj> from(VersionEnumerable<Sbj> ve) throws NoSuchVersionException {
		return from(ve, ThreadRole.MASTER, ()-> new UniversalVersion<>(ve));
	}
	
//	@Override
//	protected Object cloneNonConstant() {
//		final VersionEnumerable<Subject> ve = getAddress();
//		try {
//			return ve != null
//					? new UniversalVersion<>(ve)
//					: new UniversalVersion<>(getSubject());
//			
//		} catch (ReenterException | IncomparableException | UncertainPlaceholderException | NoSuchVersionException e) {
//			return throwTodoException(e);
//		}
//	}

	

//	@Override
//	protected Boolean cacheConstant() {
//		return true;
//	}

	/* (non-Javadoc)
	 * @see ompca.vodcg.condition.version.UbiquitousVersion#checkUbiquitous()
	 */
	@Override
	public void checkUbiquitous() {
		throwTodoException("check for the universal version");
	}

	@Override
	protected boolean derives(
			final Version<? extends Subject> newVer) {
		return (newVer != null 
				&& getAddress() == newVer.getAddress())
				|| super.derives(newVer);
	}
	
	@Override
	public boolean isDeclarator() {
		return true;
	}
	
	/* (non-Javadoc)
	 * @see ompca.vodcg.condition.version.UbiquitousVersion#enumerate(ompca.vodcg.Addressable)
	 */
	@Override
	public <E extends VersionEnumerable<? super Subject>> EnumeratedVersion<Subject, E> enumerate(E enumer)
			throws UnsupportedOperationException {
		throwTodoException("enumeration for the universal version");
		return null;
	}

	/* (non-Javadoc)
	 * @see ompca.vodcg.condition.version.Version#matches(ompca.vodcg.condition.version.ThreadPrivateVersion.ThreadRole)
	 */
	@Override
	public boolean matches(ThreadRoleMatchable newRole) {
		if (newRole != null && newRole instanceof FunctionallableRole) 
			switch (((FunctionallableRole) newRole).getBasic()) {
			case MASTER:		return true;
			case FUNCTION:
			case NON_MASTER:
			case THREAD1:
			case THREAD2:
			default:
			}
		return false;
	}
	
}