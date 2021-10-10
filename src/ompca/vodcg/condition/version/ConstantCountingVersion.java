/**
 * 
 */
package ompca.vodcg.condition.version;


import java.util.List;
import java.util.SortedSet;

import org.eclipse.cdt.core.dom.ast.IASTForStatement;

import ompca.condition.SerialFormat;
import ompca.vodcg.ASTUtil;
import ompca.vodcg.Assignable;
import ompca.vodcg.SystemElement;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.PathVariable;
import ompca.vodcg.condition.Referenceable;

/**
 * @author Kao, Chen-yi
 *
 */
public class ConstantCountingVersion<Subject extends Referenceable> 
extends Version<Subject> {
	
//	private static final Map<String, Referenceable> 
//	HIGHEST_COUNTINGS = new HashMap<>();
	
	private int count;
//	private boolean versionIsLocked = false;

	
	
	/**
	 * For subject having an ambiguous ID by default and needing counting version. 
	 * TODO? merge with {@link EnumeratedVersion}
	 * before being set.
	 * 
	 * @param count - allowed counting non-linearly
	 * @param address 
	 * @param role 
	 * @param condGen 
	 * @throws NoSuchVersionException 
	 */
	public ConstantCountingVersion(int count, VersionEnumerable<Subject> address, FunctionallableRole role) 
			throws NoSuchVersionException {
		super(address, role);
		this.count = count;
	}
	
//	public ConstantCountingVersion(Subject subject, int count, 
//			ThreadRoleMatchable role) throws NoSuchVersionException {
//		super(subject, role);
//		this.count = count;
//	}
	
//	public ConstantCountingVersion(PathVariable var, IASTForStatement loop) {
//		this(var, loop.currentCount);
//	}



	/**
	 * 		headSet(asn).size		headSet(asn2).size
	 * ------------	asn -----------	loop{ -	asn2 -------	} ----------
	 * 
	 * @param asn
	 * @param loop
	 * @return
	 */
	public static int countIn(Assignable<?> asn, IASTForStatement loop) {
		if (asn == null || testsNot(asn.isAssigned())) return -1;
		
		final VODCondGen condGen = asn.getCondGen();
		final SortedSet<Assignable<?>> asns = condGen.getWritingHistoryOfBeforeTP(asn);
		final int astCount = asns.headSet(asn).size();
		if (loop == null) return astCount;
		if (!loop.contains(asn.getTopNode())) return -1;
		
//		final ASTRuntimeLocationComputer rlc = new ASTRuntimeLocationComputer(condGen);
//		boolean meetsLv = false, isBeforeLoop = true, isAfterLoop = false;
		int count = 0;
		for (Assignable<?> asnh : asns) {
			// lv2.isAssigned()
//			if (lv2.isIteratorOf(loop)) throwTodoException("various iterating");
//			if (isBeforeLoop) {isBeforeLoop = false; count = 0; continue;}	// isIterator

			if (loop.contains(asnh.getTopNode())) count++;
			if (asnh == asn) return count;
//			if (meetsLv) return astCount - count;							// isBefore
//			else if (rlc.isIn(lv2.getTopNode(), loop)) {
//				if (isBeforeLoop) isBeforeLoop = false;							// isIn
//			} 
//			else if (!isBeforeLoop && !isAfterLoop) {
//				isAfterLoop = true; count = 0; continue;						// isAfter
//			}
		}
		return throwInvalidityException("!loop.contains(lv.getTopNode())");	
	}
	
	/**
	 * @param pv
	 * @param loop
	 * @return
	 */
	public static int countUpperBoundOf(PathVariable pv, IASTForStatement loop) {
		return ASTUtil.countNamesOfIn(pv.getASTName(), loop);
	}
	

	
//	protected Object clone() {
//		return new ConstantCountingVersion<>(getSubject(), count, getThreadRole());
//	}

	
	
	/* (non-Javadoc)
	 * @see ompca.condition.Version#getID(ompca.condition.SerialFormat, java.lang.String)
	 */
	public String getIDSuffix(SerialFormat format) {
		return super.getIDSuffix(format)	// getting my subversion's ID suffix 
				+ "_" + String.valueOf(count);
	}
	
//	/**
//	 * @return
//	 */
//	static public ConstantCountingVersion<Referenceable> getCount(Referenceable subject) {
//		return version;
//	}
	
	/**
	 * @return
	 */
	public int getCount() {
		return count;
	}
	
	
	
//	/**
//	 * @return
//	 * <pre>
//	 * 	sbj_(n+1)_sub							if sbj_n_sub
//	 */
//	public Version<Subject> appendConstantCounting() {
//		count++;
//		return this;
//	}

	/**
	 * A mutable operation.
	 * 
	 * TODO: cache to eliminate duplicates
	 * 
	 * @return Just a new decreased counting version without caring sub-versions.
	 * @see ompca.condition.version.Version#appendConstantCounting()
	 */
	public ConstantCountingVersion<Subject> decreaseCounting() {
		if (count == 0) throwInvalidityException("minus counting");
		count--;
		return this;
//		return new ConstantCountingVersion<Subject>(getSubject(), count - 1);
	}
	
	/**
	 * A mutable operation.
	 * 
	 * TODO: cache to eliminate duplicates
	 * 
	 * @return Just a new increased counting version without caring sub-versions.
	 * @see ompca.condition.version.Version#appendConstantCounting()
	 */
	public ConstantCountingVersion<Subject> increaseCounting() {
		count++;
		return this;
//		return increaseCounting(getSubject());
	}
	
	/**
	 * An immutable operation.
	 * 
	 * TODO: cache to eliminate duplicates
	 * 
	 * @return Just a new increased counting version without caring sub-versions.
	 * @see ompca.condition.version.Version#appendConstantCounting()
	 */
	public ConstantCountingVersion<Subject> cloneByIncreaseCounting(VersionEnumerable<Subject> newAddress) {
		try {
			return new ConstantCountingVersion<Subject>(count + 1, newAddress, getThreadRole());
			
		} catch (NoSuchVersionException e) {
			return throwTodoException(e);
		}
	}

	
	
	@SuppressWarnings("unchecked")
	@Override
	protected boolean equalsToCache(SystemElement e2) {
		return super.equalsToCache(e2) 
				&& ((ConstantCountingVersion<Subject>) e2).count == count;
	}
	
	protected List<Integer> hashCodeVars() {
		List<Integer> vars = super.hashCodeVars();
		vars.add(count);
		return vars;
	}

}