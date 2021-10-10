/**
 * 
 */
package ompca.vodcg.parallel;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.Elemental;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.Arithmetic;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.FunctionalPathVariable;
import ompca.vodcg.condition.ParallelCondition;
import ompca.vodcg.condition.PathVariable;
import ompca.vodcg.condition.PathVariablePlaceholder;
import ompca.vodcg.condition.Proposition;
import ompca.vodcg.condition.Relation.Operator;
import ompca.vodcg.condition.version.NoSuchVersionException;
import ompca.vodcg.condition.version.Version;

/**<pre>
 * A reduced variable is a privatized and functionalized variable, but not vice versa.
 * 
 * For reduction variable privatization and functionalization, 
 * see {@link #generateReductionAssertion()}
 * 
 * An {@link OmpReduceable} is an {@link OmpFlushable}.
 * 
 * <q>If nowait is not used, the reduction computation will be complete at the end of the construct;
however, if the reduction clause is used on a construct to which nowait is also applied, accesses to
the original list item will create a race and, thus, have unspecified effect unless synchronization
ensures that they occur after all threads have executed all of their iterations or section constructs,
and the reduction computation has completed and stored the computed value of that list item. This
can most simply be ensured through a barrier synchronization.</q>
 * </pre>
 * 
 * @see http://www.openmp.org/wp-content/uploads/openmp-4.5.pdf
 * @author Kao, Chen-yi
 *
 */
abstract public class OmpReduceable extends OmpThreadPrivatizable {

	private Operator op = null;

	final private Map<PathVariable, PathVariablePlaceholder> reductionVars = new HashMap<>();
	
	/**
	 * @param op - maybe null if there's no reduction declared.
	 * @param address
	 * @param blockStat
	 * @param nowait
	 * @param pc
	 * @param condGen
	 */
	public OmpReduceable(Operator op, IASTFileLocation address, IASTStatement blockStat, 
			boolean nowait, ParallelCondition pc, VODCondGen condGen) {
		super(address, blockStat, nowait, pc, condGen);
		this.op = op;
	}

	
	
	public PathVariablePlaceholder getReductionPlaceholder(PathVariable v) {
		if (v == null) throwNullArgumentException("path variable");
		
		return reductionVars.get(v);
	}
	
	/**
	 * @param v
	 * @param threadId - negative value means in various (non-constant) thread ID's.
	 * @return The last privatized delegate version for performing reduction.
	 * @throws NoSuchVersionException 
	 */
	@SuppressWarnings("deprecation")
	public Version<FunctionalPathVariable> getPrivatizedReductionVersion(
			PathVariable v, int threadId) throws NoSuchVersionException {
		try {
			return getThrow(()-> getReductionPlaceholder(v).getThreadPrivateVersion(
					getStatement(), threadId, peekCondition()));
			
		} catch (NoSuchVersionException e) {
			throw e;
		} catch (Exception e) {
			return throwUnhandledException(e);
//			return Version.throwNoSuchVersionException(v + "," + threadId);
		}
	}
	
	public Version<FunctionalPathVariable> getLastPrivatizedDelegate(
			PathVariable v, int threadId) throws NoSuchVersionException {
		return getPrivatizedReductionVersion(v, threadId);
	}
	
	public Operator getOperator() {
		return op;
	}
	
	/**
	 * frc1(taskm) 	= frc1(chunk*thread 					... chunk*(thread+1) - 1)
	 * 				= frc1(chunk*(nthread+thread)	 		... chunk*(nthread+thread+1) - 1)
	 * 				= ...
	 * 				= frc1(chunk*(round*nthread+thread)	 	... chunk*(round*nthread+thread+1) - 1)
	 * @return
	 */
	public ArithmeticExpression getTaskIndex() {
		throwTodoException("unimplemented method");
		return null;
	}
	
	
	
	/**<pre>
	 * 
	 * <q>2.19.3  List Item Privatization
	 * For any construct, a list item that appears in a data-sharing attribute clause, including a reduction clause, 
	 * may be privatized. Each task that references a privatized list item in any statement in the construct receives 
	 * at least one new list item if the construct has one or more associated loops, and otherwise each such task 
	 * receives one new list item.</q>
	 * (OPENMP API Specification: Version 5.0 November 2018)
	 * 
	 * Variable privatization and functionalization:
	 * 
	 * an introduced (virtual) expression at last and 
	 * trio-role (reduction, private and functional) intermediate delegates -
	 * frc1 = frc1(task0) op frc1(task1) op ... op frc1(taskm) op ...
	 * 		= TODO?
	 * 
	 * TODO?
	 * pre(blockStat) /\ numThreads = 2 -> frc1 = frc1(0) op frc1(1)                	 /\
	 * pre(blockStat) /\ numThreads = 3 -> frc1 = frc1(0) op frc1(1) op frc1(2)     	 /\
	 * 		...
	 * pre(blockStat) /\ numThreads = n -> frc1 = frc1(0) op frc1(1) op ... op frc1(n-1) /\
	 * 		...
	 * pre(blockStat) /\ numThreads = maxNumThreads -> 
	 * 		frc1 = frc1(0) op frc1(1) op … op frc1(maxNumThreads-1)   
	 * 
	 * For uninterpreted functions frc1(t) and j(t):
	 * 
	 * frc1(t) = frc1 /\ loopGeneral[t1 = t]
	 * j(t) = j /\ loopGeneral[t1 = t]
	 * 
	 * </pre>
	 * 
	 * @return
	 */
	public Proposition generateReductionAssertion() {
		if (!reducesAny()) return null;
		
		Proposition result = null;
//		if (op instanceof Arithmetic.Operator) {
//			final IASTStatement b = getBlockStatement();
//			for (PathVariableDelegate rd : reductionVars.values()) {
//				assert rd != null;
//				for (int n = 2; n <= VOPCondGen.MAX_NUM_THREADS; n++) {
//					
//					List<Expression> operands = new ArrayList<>();
//					// frc1(task0) op frc1(task1) op … op frc1(taskm)
//					for (int t = 0; t < n; t++) 
//						operands.add(rd.getThreadPrivateVersion(b, t, condition));
//					
//					// numThreads = n -> frc1 = frc1(0) op frc1(1) op … op frc1(n-1)
//					final int n_ = n;
//					Supplier<Proposition> nr = ()-> condition.getNumThreads().equal(
//							Int.from(n_)).imply(()-> rd.equal((Arithmetic) 
//							Arithmetic.from((Arithmetic.Operator) op, operands)));
//					result = result == null ? nr.get() : result.and(nr);
//				}
//			}
//		} // TODO: else ...
		return result;
	}
	
	
	
//	/**
//	 * The reduced variable that's not an array doesn't race.
//	 * 
//	 * @see OmpThreadPrivatizable#generateRaceAssertion(ArrayAccessVersion, ArrayAccessVersion, Proposition)
//	 */
//	@Override
//	protected Proposition generateRaceAssertion(
//			ArrayAccessVersion aav1, ArrayAccessVersion aav2, Proposition result) {
//		if (aav1 == null || aav2 == null) return result;
//
////		assert aav1.equalsVariable(aav2);
//		try {
//			for (ArithmeticExpression arg1 : aav1.getArguments())
//				for (PathVariablePlaceholder ap1 : 
//					arg1.toExpression().getDirectPathVariablePlaceholders()) {
//					final PathVariable apv = ap1.getVariable();
//					final Version<PathVariable> prv1 = getPrivatizedReductionVersion(apv, 1),
//							prv2 = getPrivatizedReductionVersion(apv, 2);
//					if (prv1.getSubversion(ArrayAccessVersion.class) == aav1 
//							|| prv2.getSubversion(ArrayAccessVersion.class) == aav2) {
//						final Proposition sub = super.generateRaceAssertion(aav1, aav2, result);
//						result = result == null ? sub : result.or(()-> sub);
//					}
//				}
//			return result;
//			
//		} catch (Exception e) {
//			return throwTodoException(e);
//		}
//	}
	

	
//	protected Proposition generateAssertion() {
//		Proposition superAss = super.generateAssertion(), 
//				redAss = generateReductionAssertion();
//		return superAss == null 
//				? redAss
//				: (redAss == null ? superAss : superAss.and(()-> redAss));
//	}
	

	
	/**<pre>
	 * Variable privatization:
	 * 
	 * 	frc1 = {0, ..., frc1(1), frc1(2), ..., frc1(numThreads), 0, ...} 
	 * 
	 * </pre>
	 * 
	 * @param clause
	 * @param privateArgv 
	 * @return
	 */
	public void reduce(String clause, final List<ArithmeticExpression> privateArgv) {
		if (clause == null) throwNullArgumentException("clause");
		
		Matcher mReduction = Pattern.compile(OmpUtil.patternReduction(
				null, "operator", "reductionList", null, null)).matcher(clause); 

		String opClause = null, listClause = null;
		while (mReduction.find()) {
			if (opClause == null) opClause = mReduction.group("operator"); 
			if (listClause == null) listClause = mReduction.group("reductionList");
		}
		if (opClause == null || listClause == null) return;

		op = Arithmetic.Operator.from(opClause);
		PathVariablePlaceholder rd = null;
		for (PathVariable v : parseAndPrivatize(listClause, privateArgv)) {
			for (PathVariablePlaceholder pd : getPrivatizedPlaceholders(v)) 
				if (rd == null || 
						Elemental.tests(rd.getAssignable().isBeforeLocally(pd.getAssignable())))
					rd = pd;
			if (rd == null) throwTodoException("unsupported reduction");
			else reductionVars.put(v, rd);
		}
	}

	/**
	 * @return
	 */
	public boolean reducesAny() {
		return op != null;
	}

}