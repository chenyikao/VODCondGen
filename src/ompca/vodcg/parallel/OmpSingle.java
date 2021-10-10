/**
 * 
 */
package ompca.vodcg.parallel;

import java.util.regex.Pattern;
import java.util.regex.Matcher;

import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.ParallelCondition;

/**
 * @author Kao, Chen-yi
 *
 */
public class OmpSingle extends OmpThreadPrivatizable {

	/**
	 * @param address
	 * @param blockStat
	 * @param pc
	 * @param condGen
	 */
	private OmpSingle(IASTFileLocation address, IASTStatement blockStat,
			ParallelCondition pc, VODCondGen condGen) {
		this(address, blockStat, false, pc, condGen);
	}
	
	/**
	 * @param address
	 * @param nowait
	 * @param blockStat
	 * @param pc
	 * @param condGen
	 */
	protected OmpSingle(IASTFileLocation address, IASTStatement blockStat, boolean nowait,
			ParallelCondition pc, VODCondGen condGen) {
		super(address, blockStat, nowait, pc, condGen);
	}

	/**
	 * @param clauses
	 * @param address
	 * @param blockStat
	 * @param condGen
	 * @return
	 */
	protected static OmpSingle from(String clauses, IASTFileLocation address, IASTStatement blockStat, 
			ParallelCondition pc, VODCondGen condGen) {
		assert address != null;
		
		Matcher mSingle = Pattern.compile("("
				+ OmpUtil.patternPrivate("private", "privateList", null, null)					+ "|" 
				+ OmpUtil.patternFirstPrivate("firstprivate", "firstPrivateList", null, null)	+ "|" 
				+ OmpUtil.patternNoWait("nowait")												+ "|" 
				+ "\\s" + ")+").matcher(clauses);

		final OmpSingle os = new OmpSingle(address, blockStat, pc, condGen);
		while (mSingle.find()) {
			if (mSingle.group("private") != null) os.parseAndPrivatize(mSingle.group("privateList"));
			if (mSingle.group("firstprivate") != null);	// TODO, "firstPrivateList") != null);
			if (mSingle.group("nowait") != null) os.setNowait();
		}
		return os;
		
	}

}
