/**
 * 
 */
package ompca.vodcg.condition.data;

import java.util.EnumMap;
import java.util.Map;

import ompca.Mappable;
import ompca.vodcg.condition.Arithmetic;
import ompca.vodcg.condition.Relation;

/**
 * @author Kao, Chen-yi
 *
 */
public class BitsGuard extends ArithmeticGuard {

	public enum Operator implements Relation.Operator {
		BitAnd;
		
		/* (non-Javadoc)
		 * @see ompca.condition.Relation.Operator#isAssociativeTo(ompca.condition.Relation.Operator)
		 */
		@Override
		public boolean isAssociativeTo(Relation.Operator op) {
			return false;
		}
		@Override
		public boolean isCommutative() {
			return Enum.valueOf(Arithmetic.Operator.class, name()).isCommutative();
		}
		
		@Override
		public <M extends Map<?,?>> EnumMap<? extends Key, M> createPartitionMap() {
			return new EnumMap<>(Operator.class);
		}
		
		@Override
		public <M extends Mappable<?, ?>> EnumMap<? extends Key, M> createPartitionMappable() {
			return new EnumMap<>(Operator.class);
		}
		
		
		
		/* (non-Javadoc)
		 * @see ompca.condition.Relation.Operator#negate()
		 */
		@Override
		public ompca.vodcg.condition.Relation.Operator negate() {
			switch (this) {
			default:			return null;
			}
		}
		
		public java.lang.String toString() {
			switch (this) {
			case BitAnd:			return "&guard";
			default:
				assert(false); return null;	// should NOT come here!
			}
		}
		
		public <H extends Relation> java.lang.String toZ3SmtString(
				H host, boolean printsVariableDeclaration, boolean printsFunctionDefinition) {
			switch (this) {
			case BitAnd:			return "bvand";
			default:
				assert(false); return null;	// should NOT come here!
			}
		}
		
	}
	
	
	
	/**
	 * @param arith - arithmetic to guard
	 */
	private BitsGuard(final Arithmetic arith) {
		super(arith);
	}
	
	public static BitsGuard from(final Arithmetic arith) {
		return (BitsGuard) from(
				arith, ()-> new BitsGuard(arith));
	}
	
}