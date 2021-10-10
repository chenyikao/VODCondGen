/**
 * 
 */
package ompca.vodcg.parallel;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.vodcg.ASTAddressable;
import ompca.vodcg.Assignable;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.Arithmetic;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.Equality;
import ompca.vodcg.condition.Expression;
import ompca.vodcg.condition.ParallelCondition;
import ompca.vodcg.condition.Proposition;
import ompca.vodcg.condition.Proposition.True;
import ompca.vodcg.condition.Variable;
import ompca.vodcg.condition.VariablePlaceholder;
import ompca.vodcg.condition.data.NumericExpression;
import ompca.vodcg.condition.version.ArrayAccessVersion;
import ompca.vodcg.condition.version.FunctionalVersion;
import ompca.vodcg.condition.version.NoSuchVersionException;
import ompca.vodcg.condition.version.ThreadRole;

/**
 * @author Kao, Chen-yi
 *
 */
public class OmpSimd extends OmpDirective {

	protected OmpSimd(IASTFileLocation address, IASTStatement blockStat, ParallelCondition pc,
			VODCondGen condGen) {
		super(address, blockStat, pc, condGen);
		// TODO Auto-generated constructor stub
	}



	/**
	 * For example,
	 * #pragma omp simd
	 * for (i=0;i<len-1;i++)
	 * 	a[i+1]=a[i]+b[i];
	 * 
	 * => 
	 * 
	 * (simd_c(i) = simd_a(i) + simd_b(i) 
	 * 	&& simd_a(i) = a[i] && simd_b(i) = b[i] && simd_c(i) = a[i+1])
	 * 	&& exists i1, i2, i1 = i2 => simd_c(i1) != simd_c(i2) 
	 */
	@Override
	protected Proposition cacheRaceAssertion() {
		Proposition race = super.cacheRaceAssertion();
		final IASTStatement stat = getStatement();
		if (stat instanceof IASTForStatement) {
			final ASTAddressable rtAddr = getRuntimeAddress();
			final VODCondGen cg = getCondGen();
			
			for (IASTNode child : ((IASTForStatement) stat).getBody().getChildren()) 
				if (child instanceof IASTInitializerClause) {
					final Expression ce = Expression.fromRecursively((IASTInitializerClause) child, rtAddr, cg);
					if (ce instanceof Equality) try {
						final Proposition simd = toProposition(
								(FunctionalVersion) FunctionalVersion.from(
										Assignable.fromCanonicalIteratorOf((IASTForStatement) stat, rtAddr, cg)), 
								(Equality) ce);
						race = race == null ? simd : race.or(simd);
					} catch (NoSuchVersionException e) {
						throwTodoException(e);
					}
				}
		} else 
			throwTodoException("unsupported block statement");
		
		return race;
	}



	public static OmpSimd from(IASTFileLocation address, IASTStatement stat, ParallelCondition pc,
			VODCondGen condGen) {
		return new OmpSimd(address, stat, pc, condGen);
	}
	
	
	
	private Proposition toProposition(FunctionalVersion idxFv, Equality eq) {
		assert eq != null;
		final Expression asner = eq.getAssigner();
		final Arithmetic a = asner instanceof Arithmetic ? (Arithmetic) asner : null;
		final List<? extends Expression> asners = a != null ? a.toList() : Collections.singletonList(asner);
		final Arithmetic.Operator op = a != null ? a.getOp() : null;
		
		final VariablePlaceholder<?> idx = VariablePlaceholder.fromNonAST(idxFv);
		final List<VariablePlaceholder<?>> simdAsners = new ArrayList<>();
		Proposition p = True.PureTrue;
		
		//	&& simd_a(i) = a && simd_b(i) = b && simd_c(i) = c)
		for (Expression asnr : asners) {
			final VariablePlaceholder<?> simdAsnerOprd = toSimd(idx, asnr);
			simdAsners.add(simdAsnerOprd);
			p = p.and(()-> simdAsnerOprd.equal((NumericExpression) asnr));
			simdAsnerOprd.setAssigner(asnr);
		}
		
		// (c = a op b && simd_c(i) = simd_a(i) op simd_b(i) 
		final VariablePlaceholder<?> simdAsd = toSimd(idx, eq.getAssigned());
		final Expression simdAsner = op == null 
				? simdAsners.get(0) 
				: Arithmetic.from(op, simdAsners);
		p = p.and(()-> eq.and(()-> simdAsd.equal((NumericExpression) simdAsner)));
		simdAsd.setAssigner(simdAsner);
		
		// 	&& exists i1, i2, i1 = i2 -> simd_c(i1) != simd_c(i2) 
		final VariablePlaceholder<?> i1 = VariablePlaceholder.fromNonAST(idxFv.cloneIfChangeRole(ThreadRole.THREAD1)),
				i2 = VariablePlaceholder.fromNonAST(idxFv.cloneIfChangeRole(ThreadRole.THREAD2));
		final ArithmeticExpression simdAsd1 = simdAsd.cloneReindex(idx, i1),
				simdAsd2 = simdAsd.cloneReindex(idx, i2);
		p = p.and(()-> i1.equal(i2).imply(()-> simdAsd1.equal(simdAsd2).not()));
		return p;
	}



	/**
	 * @param idx - <code>i</code>
	 * @param scalar - <code>a</code>
	 * @return  - <code>simd_a(i)</code>
	 */
	@SuppressWarnings("unchecked")
	private VariablePlaceholder<?> toSimd(VariablePlaceholder<?> idx, Expression scalar) {
		assert idx != null && scalar != null;
		final IASTStatement block = getStatement();
		final VariablePlaceholder<? extends Variable> simdp = VariablePlaceholder.fromNonAST(
				"_simd_" + scalar.getID(null), scalar.getType(), false, null, ()-> scalar.getFunctionScope(), block, getCondGen());
		try {
			((VariablePlaceholder<Variable>) simdp).setVersion(
					ArrayAccessVersion.from(Arrays.asList(idx), null, simdp, ThreadRole.FUNCTION));
		} catch (NoSuchVersionException e) {
			throwTodoException(e);
		}
		return simdp;
	}
	
}