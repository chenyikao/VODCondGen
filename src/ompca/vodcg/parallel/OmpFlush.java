package ompca.vodcg.parallel;

import java.util.regex.Pattern;
import java.util.regex.Matcher;

import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.ParallelCondition;
import ompca.vodcg.condition.Proposition;

/**
 * @author Kao, Chen-yi
 *
 */
public class OmpFlush extends OmpFlushable {

	/**
	 * @param address
	 * @param blockStat
	 * @param condGen
	 */
	protected OmpFlush(IASTFileLocation address, IASTStatement blockStat, ParallelCondition pc,
			VODCondGen condGen) {
		super(address, blockStat, false, pc, condGen);
	}

	/**
	 * @param clauses
	 * @param address
	 * @param blockStat
	 * @param condGen
	 * @return
	 */
	protected static OmpFlush from(String clauses, IASTFileLocation address, IASTStatement blockStat, 
			ParallelCondition pc, VODCondGen condGen) {
		assert address != null;
		
		Matcher mFlush = Pattern.compile("("
				+ OmpUtil.patternParenthesizedList("list", null, null)	+ "|" + "\\s" + ")+")
				.matcher(clauses);
		
		OmpFlush of = new OmpFlush(address, blockStat, pc, condGen);
		
		String fList = mFlush.group("list");
		if (fList != null) ;	// TODO
		return of;
	}


	
	@Override
	protected Proposition cacheRaceAssertion() {
		return null;
	}
	
}
