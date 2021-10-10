package ompca.vodcg.parallel;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.vodcg.Assignable;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.ParallelCondition;
import ompca.vodcg.condition.PathVariablePlaceholder;

/**<q>
 * The FLUSH directive is implied for the directives shown in the table below. 
 * The directive is not implied if a NOWAIT clause is present.
 * 
 * C / C++:
 * 
    barrier
    parallel - upon entry and exit
    critical - upon entry and exit
    ordered - upon entry and exit
    for - upon exit
    sections - upon exit
    single - upon exit
    </q> 
    
 * @author Kao, Chen-yi
 * @see https://computing.llnl.gov/tutorials/openMP/#FLUSH
 *
 */
abstract public class OmpFlushable extends OmpDirective {
	
	private boolean noWait = false;
	
	public OmpFlushable(IASTFileLocation address, IASTStatement blockStat, 
			boolean nowait, ParallelCondition pc, VODCondGen condGen) {
		super(address, blockStat, pc, condGen);
		noWait = nowait;
	}
	
	

	/**
	 * The directive is not implied if a NOWAIT clause is present.
	 * @return
	 */
	public boolean canFlush() {
		return !getNowait();
	}
	
	public boolean isSynchronized() {
		return !getNowait();
	}
	
	final public boolean getNowait() {
		return noWait;
	}

	protected Set<PathVariablePlaceholder> getArrayEnclosersLike(PathVariablePlaceholder arrayEncloser) {
		assert arrayEncloser != null;
		final Set<PathVariablePlaceholder> aes = new HashSet<>();
		for (Assignable<?> asn : Assignable.fromOf(
				getStatement(), arrayEncloser.getASTName(), cacheRuntimeAddress(), getCondGen()))
			aes.add(asn.getPathVariablePlaceholder());
		return aes;
	}
	
	final protected void setNowait() {
		noWait = true;
	}
	
	/**
	 * @param parallelRegion
	 */
	protected void setParallelRegion(OmpParallel parallelRegion) {
		super.setParallelRegion(parallelRegion);
		parallelRegion.add(this);
	}

}