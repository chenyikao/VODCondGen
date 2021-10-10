package ompca.vodcg.condition.version;

import ompca.Cluster;
import ompca.condition.SerialFormat;
import ompca.vodcg.condition.Expression;
import ompca.vodcg.condition.Referenceable;

/**
 * Enumerated versions are serialized on top with formats Z3/Z3-SMT
 * while they can be objected-ly subversion-ed.
 * 
 * @author Kao, Chen-yi
 *
 */
public class EnumeratedVersion
<Subject extends Referenceable, E extends VersionEnumerable<? super Subject>> 
extends Version<Subject> implements UbiquitousVersion<Subject> {

	private static class EnumerCluster
	<E extends VersionEnumerable<? extends Referenceable>> extends Cluster<E> {

		/**
		 * @param kernel
		 */
		EnumerCluster(E kernel) {
			super(kernel);
		}

		/**
		 * @param format
		 * @return
		 */
		public String getShortAddress(SerialFormat format) {
			assert kernel != null;
			return kernel.getShortAddress(format);
		}
		
//		@Override
//		public Set<VariablePlaceholder<?>> getVariableReferences() {
//			assert kernel != null;
//			return kernel.getDirectVariableReferences();
//		}
		
		/**
		 * addr_n-m2: reversions()	=> last version (cluster)
		 * 	...
		 * addr_n-m1				=> c2?
		 * 	...
		 * addr_n					=> current version (cluster)
		 * 	...
		 * addr_n+l1				=> c2?
		 * 	...
		 * addr_n+l2: reversions()	=> next version (cluster)
		 * 
		 * @see ompca.Cluster#equals(ompca.Cluster)
		 */
		@Override
		protected boolean equals(Cluster<E> c2) {
			if (!(c2 instanceof EnumerCluster)) return false;
			
			E e2 = ((EnumerCluster<E>) c2).kernel;
			if (matchesFrom(e2, kernel)) return true;	// traversing kernel -> last version
			if (matchesFrom(kernel, e2)) return true;	// traversing e2 -> last version
			return false;
		}
		
		static private boolean matchesFrom(
				final VersionEnumerable<?> target, VersionEnumerable<?> begin) {
			assert begin != null;
			while (begin != target) {
				begin = (VersionEnumerable<?>) begin.previous();
				if (begin == null || begin.reversions()) return false;
			}
			return true;
		}

		/* (non-Javadoc)
		 * @see ompca.Cluster#hashCluster()
		 */
		@Override
		protected int hashCluster() {
			return getShortAddress(null).hashCode();
		}

	}
	
	
	
	private EnumerCluster<E> cluster;

	@SuppressWarnings("unchecked")
	private EnumeratedVersion(E e, EnumerCluster<E> ec, 
			FunctionallableRole role) throws NoSuchVersionException {
		super((VersionEnumerable<Subject>) e, role);
		
		if (ec == null) throwNullArgumentException("enumeration scope");
		cluster = ec;
		setAddressName(cluster.getShortAddress(null));
	}

	@SuppressWarnings({ "unchecked" })
	public static <Subject extends Referenceable, E extends VersionEnumerable<Subject>> 
	Version<Subject> from(E enumer, final FunctionallableRole role) 
			throws NoSuchVersionException {
		if (enumer == null) throwNullArgumentException("enumer");
		if (role == null) throwNullArgumentException("role");
		
//		if (role.isPrivate()) 
//			throwNoSuchVersionException((VersionEnumerable<Subject>) enumer, enumer.getThreadRole(), role);

		enumer = enumer.previousOrUnambiguousAssigned();
		if (enumer.isThreadPrivate()) 
			throwNoSuchVersionException((VersionEnumerable<Subject>) enumer);
		if (tests(enumer.isConstant()) || role == ThreadRole.CONST) 
			throwNoSuchVersionException(enumer);

		final boolean isA = tests(enumer.isAssigned());
		if (isA && enumer.isLoopIterator()) throwNoSuchVersionException(enumer);
		
		if (!enumer.isDeclarator() && !enumer.isParameter() && !isA) 
			return from((E) enumer.previousRuntimes(), role);
//			return sbj.debugCallDepth(()->
//			from(sbj, (E) enumer.previousRuntime(), role));
		
		final E enumer_ = enumer;
		return fromSubversion(enumer, role, 
				()-> new EnumeratedVersion<>(enumer_, new EnumerCluster<>(enumer_), role));
	}

	
	
//	/**
//	 * Serialization-based subversion ID insertion.
//	 * 
//	 * @see ompca.vodcg.condition.version.Version#getSubversionID(ompca.vodcg.condition.SerialFormat, java.lang.String)
//	 */
//	public String getIDSuffix(SerialFormat format) {
//		return "_" + cluster.getShortAddress(format) + 
//				super.getIDSuffix(format);	// getting my subversion's ID suffix
//	}
	
//	@Override
//	public Set<Version<Variable>> getDirectVariableReferences() {
//		assert cluster != null;
//		return cluster.getVariableReferences();
//	}
	


//	@Override
//	protected Object cloneNonConstant() {
//		@SuppressWarnings("unchecked")
//		EnumeratedVersion<Subject, E> clone = (EnumeratedVersion<Subject, E>) super.cloneNonConstant();
//		clone.cluster = (EnumerCluster<E>) clone.cluster;
//		return clone;
//	}

	
	
	/* (non-Javadoc)
	 * @see ompca.vodcg.condition.version.UbiquitousVersion#checkUbiquitous()
	 */
	@Override
	public void checkUbiquitous() {
		throwTodoException("replace all non-enumerated versions");
	}

//	/**
//	 * For both {@link EnumeratedVersion}'s identical name is the <em>only</em> 
//	 * derivation constraint.
//	 *  
//	 * @param newVer
//	 * @return
//	 */
//	@Override
//	protected boolean derives(Version<?> newVer) {
//		if (newVer instanceof EnumeratedVersion) {
//			final String sbjName = getSubject().getName();
//			if (sbjName == null || sbjName.isEmpty()) 
//				throwNullArgumentException("subject name");
//			return sbjName.equals(newVer.getSubject().getName());
//		}
//		return super.derives(newVer);
//	}
	
	
	
	@SuppressWarnings("unchecked")
	@Override
	public Boolean dependsOn(Expression e2) {
		if (e2 instanceof EnumeratedVersion) try {
			return isPreviousRuntimes((EnumeratedVersion<Subject, E>) e2);
			
		} catch (ClassCastException e) {
			return false;
		}
		return super.dependsOn(e2);
	}

	public boolean isPreviousRuntimes(final EnumeratedVersion<Subject, E> ev2) {
		if (ev2 == null) throwNullArgumentException("enumerated version");
		return getAddress().isPreviousRuntimes(ev2.getAddress()); 
	}
	
	/**
	 * @param ev2
	 * @return
	 */
	public boolean equalsEnumer(EnumeratedVersion<?, ?> ev2) {
		if (ev2 == null) return false;
		
		EnumerCluster<?> enum2 = ev2.cluster;
		return cluster == null ? enum2 == null : cluster.equals(enum2);
	}

//	/* (non-Javadoc)
//	 * @see ompca.vodcg.condition.Version#equals(ompca.vodcg.condition.Version)
//	 */
//	@SuppressWarnings("unchecked")
//	@Override
//	protected boolean equalsToCache(SystemElement e2) {
//		return equalsEnumer((EnumeratedVersion<Subject, E>) e2);
//	}
	
//	@Override
//	protected List<Integer> hashCodeVars() {
//		assert cluster != null;
//		return Arrays.asList(cluster.hashCode());
//	}
	
	
	
	/* (non-Javadoc)
	 * @see ompca.vodcg.condition.version.UbiquitousVersion#enumerate(ompca.vodcg.Addressable)
	 */
	@SuppressWarnings({ "unchecked", "hiding" })
	@Override
	public <E extends VersionEnumerable<? super Subject>> EnumeratedVersion<Subject, E> enumerate(E enumer)
			throws UnsupportedOperationException {
		if (enumer == null) return (EnumeratedVersion<Subject, E>) this;
		
		throwTodoException(enumer.getShortAddress());
		return null;
	}
	
	@Override
	public void subversion(Version<? extends Subject> newSub) {
		super.subversion(newSub);
		
		assert newSub != null;
		if (!getID(null).contains(cluster.getShortAddress(null)))
			throwInvalidityException("conflict sub-version?");
	}
	
}