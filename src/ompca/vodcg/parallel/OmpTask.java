/**
 * 
 */
package ompca.vodcg.parallel;

import java.util.HashSet;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.vodcg.ASTAddressable;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.Expression;
import ompca.vodcg.condition.Forall;
import ompca.vodcg.condition.ParallelCondition;
import ompca.vodcg.condition.Proposition;
import ompca.vodcg.condition.Relation.Operator;
import ompca.vodcg.condition.VariablePlaceholder;

/**
 * @author Kao, Chen-yi
 *
 */
public class OmpTask extends OmpReduceable {

	private Object depend = null;
	
	private OmpTask(Operator op, IASTFileLocation address, IASTStatement stat, boolean nowait, ParallelCondition pc,
			VODCondGen condGen) {
		super(op, address, stat, nowait, pc, condGen);
	}
	
	
	
	/**
	 * @param clauses
	 * @param address
	 * @param blockStat
	 * @param condGen
	 * @return
	 */
	protected static OmpTask from(String clauses, IASTFileLocation address, IASTStatement blockStat, 
			ParallelCondition pc, VODCondGen condGen) {
		assert address != null;
		if (clauses != null && !clauses.isBlank()) throwTodoException("unsupported clauses");
		
		Matcher mTask = Pattern.compile("("
				+ OmpUtil.patternPrivate("private", "privateList", null, null)					+ "|" 
				+ OmpUtil.patternFirstPrivate("firstprivate", "firstPrivateList", null, null)	+ "|" 
				+ "\\s" + ")*").matcher(clauses);
		
		/* <quote href="https://www.openmp.org/spec-html/5.0/openmpsu46.html#x70-2000002.10.1">
		 * The encountering thread may immediately execute the task, or defer its execution. 
		 * In the latter case, any thread in the team may be assigned the task. 
		 * Completion of the task can be guaranteed using task synchronization constructs. 
		 * If a task construct is encountered during execution of an outer task, 
		 * the generated task region corresponding to this construct is not a part of the outer task region 
		 * unless the generated task is an included task.
		 * </quote>
		 */
		Operator op = null;
		boolean nowait = true;
		final OmpTask ot = new OmpTask(op, address, blockStat, nowait, pc, condGen);
		while (mTask.find()) {
			if (mTask.group("private") != null) ot.parseAndPrivatize(mTask.group("privateList"));
			if (mTask.group("firstprivate") != null);	// TODO, "firstPrivateList") != null);
		}
		return ot;
	}

	/**
	 * @return a task copy keeping (copying) the statement but changing the runtime address
	 */
	@SuppressWarnings("unchecked")
	@Override
	protected OmpTask cloneChangeAddressTo(ASTAddressable newRtAddr) {
		if (!(newRtAddr instanceof OmpTask)) throwTodoException("inconsistent addresses");
//		if (getStatement().isFrozen()) throwTodoException("inconsistent addresses");

		return new OmpTask(getOperator(), 
				((OmpTask) newRtAddr).getAddress(), 
				getStatement().copy(IASTNode.CopyStyle.withLocations), 
				getNowait(), 
				getCondition(), 
				getCondGen());
	}
	
	
	
	/**
	 * @return the task interchanging race. For example 
	 * 
	 * 	(i1 = 1 && i2 = 2) !<=> (i1 = 2 && i2 = 1), given
	 * 
	 * <code>
	 * int main() {
	 * 	int i;
	 * #pragma omp parallel
	 * #pragma omp single
	 * #pragma omp task
	 * 	i = 1;
	 * #pragma omp task
	 * 	i = 2;
	 * 	printf("%d", i);
	 * }
	 * </code>
	 */
	@Override
	protected Proposition cacheRaceAssertion() {
		final OmpTask pre = previous();
		if (pre == null || !dependsOn(pre) || declaresDependsOn(pre)) return null;
		
		return getInterchangeableAssertion(pre).not();
	}

	private boolean declaresDependsOn(OmpTask task2) {
		assert task2 != null;
		return depend == task2;
	}
	
	/**
	 * @param task2
	 * @return false if this task and <code>task2</code> are interchangeable to each other.
	 */
	public boolean dependsOn(OmpTask task2) {
		if (task2 == null) throwNullArgumentException("task");
		
		// pragma clause declaration dependency
		if (declaresDependsOn(task2)) return true;
		
		// propositional dependency
		if (tests(()->
		toProposition().dependsOn((Expression) task2.toProposition()))) return true;

		// interchangeable dependency (when AST API allows interchanging statements)
		return isInterchangeableTo(task2);
	}
	
	/**
	 * Task1 and Task2 are interchangeable => 
	 * 	forall v, task1p(v) && task2p(v) <=> task2pre(v) && task1post(v)
	 * 
	 * @param task2
	 * @return
	 */
	public boolean isInterchangeableTo(OmpTask task2) {
		return getInterchangeableAssertion(task2) != null;
	}
	

	
	/**
	 * @return forall v, task1p(v) && task2p(v) <=> task2pre(v) && task1post(v)
	 */
	private Proposition getInterchangeableAssertion(OmpTask task2) {
		assert task2 != null;
		
//		final IASTStatement t1block = getStatement(), t2block = task2.getStatement();
//		final INodeFactory nf = t1block.getTranslationUnit().getASTNodeFactory();
//		final IASTCompoundStatement t1t2stat = nf.newCompoundStatement(), t2t1stat = nf.newCompoundStatement();
//		t1t2stat.addStatement(t1block.copy(IASTNode.CopyStyle.withLocations));
//		t1t2stat.addStatement(t2block.copy(IASTNode.CopyStyle.withLocations));
//		t2t1stat.addStatement(t2block.copy(IASTNode.CopyStyle.withLocations));
//		t2t1stat.addStatement(t1block.copy(IASTNode.CopyStyle.withLocations));

		final Proposition t11prop = getStatementProposition(),
				t22prop = task2.getStatementProposition(),
				t21prop = task2.cloneChangeAddressTo(this).getStatementProposition(),
				t12prop = cloneChangeAddressTo(task2).getStatementProposition(),
				t1t2prop = t11prop.iff(()-> t22prop),
				t2t1prop = t21prop.iff(()-> t12prop);
		final Set<VariablePlaceholder<?>> qs = new HashSet<>(t1t2prop.getDirectVariablePlaceholders());
		qs.addAll(t2t1prop.getDirectVariablePlaceholders());
		return Forall.from(qs, t1t2prop.iff(()-> t2t1prop));
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public OmpTask previous() {
		OmpDirective pd = super.previous();
		while (pd != null && !(pd instanceof OmpTask)) {
			pd = pd.previous(); 
		}
		return (OmpTask) pd;
	}

	/**
	 * @return also task assertion of the block statement
	 */
	@Override
	public Proposition toProposition() {
		return super.toProposition().and(()-> 
		getStatementProposition());
	}

}