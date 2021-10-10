package ompca.vodcg.condition;

import java.util.EnumMap;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTCastExpression;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTNamedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTPointerOperator;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTTypeId;

import ompca.Mappable;
import ompca.vodcg.ASTAddressable;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.data.DataType;
import ompca.vodcg.condition.data.PlatformType;
import ompca.vodcg.condition.data.PointerType;

/**
 * Special kind of function call to the <em>language (C/C++, Z3, etc.) built-in</em>
 * cast functions.
 * 
 * @author Kao, Chen-yi
 *
 */
public class CastCall 
extends Relation implements ArithmeticExpression	// TODO:, FunctionalRelation 
{

	public static enum Operator implements Relation.Operator {
		Primitive, 	// for primitive casting
		Pointer;	// for pointer (object) casting
		
		private PlatformType castType = null;
		private Expression operand = null;
		
		
		
		static private Operator from(
				final IASTCastExpression cast, final ASTAddressable dynaAddr, final VODCondGen condGen) {
			if (cast == null) throwNullArgumentException("cast expression");
			
			PlatformType ct = null;
			Expression operand = null;
			switch (cast.getOperator()) {
//			case IASTCastExpression.op_last: 				
			case IASTCastExpression.op_cast:
				final IASTTypeId type = cast.getTypeId();
				final IASTExpression oprd = cast.getOperand();
				
				operand = Expression.fromRecursively(oprd, dynaAddr, condGen);
				if (operand == null) 
					throwTodoException("unsupported cast operand");
				
				final IASTDeclSpecifier decl = type.getDeclSpecifier();
				if (decl instanceof IASTSimpleDeclSpecifier)
					// for primitive type cast
					ct = DataType.from((IASTSimpleDeclSpecifier) decl);
				else if (decl instanceof IASTNamedTypeSpecifier) {
					// for pointer cast
					ct = DataType.from(((IASTNamedTypeSpecifier) decl).getName());
					if (ct instanceof DataType) 
						ct = PointerType.from((DataType) ct); 
				}
				else throwTodoException("unsupported cast type");
				for (@SuppressWarnings("unused") IASTPointerOperator p : type.getAbstractDeclarator().getPointerOperators())
					ct = PointerType.from(ct); 
				break;
				
			default:
			}
			
			return ct != null
					? from(ct, operand)
					: throwTodoException("unsupported casting");
		}
		
		static private Operator from(final PlatformType castType, Expression operand) {
			Operator op = castType instanceof DataType ? Primitive : Pointer;
			op.set(castType, operand);
			return op; 
		}
		
		@Override
		public Boolean isConstant() {return operand.isConstant();}
		@Override
		public Boolean isUnary() {return true;}
		
		@Override
		public <M extends Map<?,?>> EnumMap<? extends Key, M> createPartitionMap() {
			return new EnumMap<>(Operator.class);
		}
		
		@Override
		public <M extends Mappable<?, ?>> EnumMap<? extends Key, M> createPartitionMappable() {
			return new EnumMap<>(Operator.class);
		}
		
		
		
		/**
		 * @return
		 */
		public PlatformType getCastType() {
			return castType;
		}
		
		public Expression getOperand() {
			return operand;
		}
		
		private void set(PlatformType ct, Expression oprd) {
			castType = ct;
			operand = oprd;
		}
		
		/* (non-Javadoc)
		 * @see ompca.conditionion.Operator#negate()
		 */
		@Override
		public Operator negate() {
			throwTodoException("storing casting history for inversion");
			return null;
		}
		

		
		public java.lang.String toString() {
			final java.lang.String ctStr = castType.toString();
			java.lang.String str = "(" + ctStr;
//			switch (this) {
//			case Primitive: break;
//			case Pointer:	str += " *"; break;
//			default:
//				throwTodoException("unsupported casting");
//				assert false; return null;	// should NOT come here!
//			}
			return str + ")"; 
		}
		
		
		
		public <H extends Relation> java.lang.String toZ3SmtString(
				H host, boolean printsVariableDeclaration, boolean printsFunctionDefinition) {
			if (castType instanceof DataType) switch ((DataType) castType) {
			case Int: 	return "to_int";	
			case Real:	return "to_real";
			case Bool:	return "to_bool";	// TODO
			case Char:	return "to_char";	// TODO: ompca.ompca.conditionoCastString(SerialFormat.Z3_SMT);
			case Void:	break;	// (Void) as pointer cast
			default:
				throwTodoException("unsupported casting?");
				assert false; return null;	// should NOT come here!
			} 
				
			return castType.toZ3SmtString(printsFunctionDefinition, printsFunctionDefinition);
		}
	}

	/**
	 * @param cast
	 * @param condGen
	 */
	public CastCall(IASTCastExpression cast, final ASTAddressable rtAddr, VODCondGen condGen) {
		super(Operator.from(cast, rtAddr, condGen), rtAddr, condGen, false);	// can't invoke non-static getOp() in the constructor

		setOnlyOperand(((Operator) getOp()).getOperand());
		setFinal();
	}

	public CastCall(final PlatformType castType, Expression operand) {
		this(Operator.from(castType, operand), operand);
		
		setOnlyOperand(operand);
		setFinal();
	}
	
	/**
	 * Copy constructor.
	 * @param op
	 * @param operand
	 */
	private CastCall(Operator op, Expression operand) {
		super(op, operand);
	}

//	public Object clone() {
//		@SuppressWarnings("unchecked")
//		CastCall clone = (CastCall) super.clone();
//		clone.op = new Operator(op);
//		return clone;
//	}
	

	
	/* (non-Javadoc)
	 * @see ompca.conditompca.conditione()
	 */
	@Override
	public PlatformType getType() {
		return ((Operator) getOp()).getCastType();
	}


	
	public Boolean isZero() {
		return ((ArithmeticExpression) getFirstOperand()).isZero();
	}
	
	public Boolean isPositive() {
		return ((ArithmeticExpression) getFirstOperand()).isPositive();
	}
	
	public Boolean isPositiveOrZero() {
		return ((ArithmeticExpression) getFirstOperand()).isPositiveOrZero();
	}
	
	public Boolean isPositiveInfinity() {
		return ((ArithmeticExpression) getFirstOperand()).isPositiveInfinity();
	}
	
	public Boolean isNegative() {
		return ((ArithmeticExpression) getFirstOperand()).isNegative();
	}
	
	public Boolean isNegativeInfinity() {
		return ((ArithmeticExpression) getFirstOperand()).isNegativeInfinity();
	}
	

	
	public Expression inverse() {
		throwTodoException("storing casting history for inversion");
		return null;
	}

	@Override
	public Expression negate() {
		return new CastCall((Operator) getOp().negate(), getFirstOperand());
	}

}