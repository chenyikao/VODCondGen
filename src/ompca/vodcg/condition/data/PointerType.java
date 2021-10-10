/**
 * 
 */
package ompca.vodcg.condition.data;

import java.util.ArrayList;
import java.util.List;

import ompca.Elemental;
import ompca.condition.SerialFormat;
import ompca.vodcg.Assignable;
import ompca.vodcg.SystemElement;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.Expression;
import ompca.vodcg.condition.Proposition;

/**
 * A unified pointing/de-pointing type accessing interface.
 * The pointing operand denotes some type instead of path-variable placeholder
 * hence the evaluation is different from one of a pointer instance.
 * 
 * A pointer type is always constant (in a global scope).
 * 
 * @author Kao, Chen-yi
 *
 */
public class PointerType extends Pointer 
implements PlatformType {		// for pointing/de-pointing types

	public static final PointerType NULL_POINTER_TYPE = new PointerType();
	
//	protected static final UnsupportedOperationException UNSUPPORTED_EXCEPTION = 
//			new UnsupportedOperationException();

	
	
	private DataType primitive = null;
	
	
	
	/**
	 * @param isFinal - true only if construction-time temporary non-final
	 */
	protected PointerType(boolean isFinal) {
		super(Operator.Point, null, isFinal); 
	}
	
	/**
	 * @param type - the primitive (element) type
	 */
	protected PointerType(DataType type) {
		this(false);
		pointToPrimitive(type);
	}
	
	protected PointerType(PointerType fromInstance) {
		this(false);

		if (fromInstance == null) throwInvalidityException(
				"Null pointer type should be created in the static way!");
		pointTo((PlatformType) fromInstance);
	}

	private PointerType() {
		super(Operator.Point); 
		pointToPrimitive(DataType.Void);
	}
	
	public static PointerType from(ArithmeticExpression ae) {
		if (ae == null) throwNullArgumentException("arithmetic expression");
		if (ae instanceof Pointer) return from((Pointer) ae);
		return from((DataType) ae.getType());
//		return throwTodoException("unsupported arithmetic expression");
	}
	
	public static PointerType from(PlatformType type) {
		if (type == null) throwNullArgumentException("type");
		return type instanceof DataType
				? new PointerType((DataType) type)
				: from((Pointer) type);	// type instanceof PointerType
	}
	
	public static PointerType from(Pointer pt) {
		if (pt == null) throwNullArgumentException("pointer");
		
		// TODO: cache pointer types, including NULL_POINTER_TYPE

		// including NULL_POINTER_TYPE
		// this == *(null) ::= null	=> this.type == (null *)
		// this == &(null) 			=> this.type == (null *)
		if (pt instanceof PointerType) return (PointerType) pt;
		
//		switch ((Operator) pt.getOp()) {
//		case Depoint:
//			// this == &const 	=> this.type == (const.type *)
//			// this == &var 	=> this.type == (var.type *)
//			// this == &pt 		=> this.type == (pt.type *)
//			return pt;
//			
//		case Point:
//			// this == *const 	=> this.type == void
//			// this == *var 	=> this.type == *(var.type)
//			// this == *pt 		=> this.type == *(pt.type)
//			return Elemental.getAltException(()-> ((SystemElement) end).isConstant() 
//					? DataType.Void
//					// if (np instanceof Pointer) return ((Pointer) np).getType();
//					: end.getType(), end.getType());	
//			
//		default:
//			break;
//		}
		final ArithmeticExpression npt = pt.nextPointing();
		if (npt == null) 
			return NULL_POINTER_TYPE; 
		if (npt instanceof Pointer) 
			return new PointerType(PointerType.from((Pointer) npt));
		
		// npt may be a pointer-type PathVariablePlaceholder
		final PlatformType nptt = npt.getType();
		return nptt instanceof DataType
				? new PointerType((DataType) nptt)
				: Elemental.get(()-> new PointerType((PointerType) nptt),
						e-> throwTodoException("nptt should be PointerType"));
				
//		try {
//		} catch (Exception e) {
//			return throwTodoException(e);
//		}
	}
	
//	public static PointerType from(
//			IASTCastExpression cast, VODCondGen condGen) {
//		if (cast == null) throwNullArgumentException("cast");
//		
//		IASTPointerOperator[] castPointers = 
//				cast.getTypeId().getAbstractDeclarator().getPointerOperators();
//		if (castPointers == null || castPointers.length == 0) return null;
//		
//		return new Pointer(Operator.Point, 
//				pointFromRecursively(operand, condGen), condGen);
//	}
	
	
	
//	public Type depointFromType() {
//		final Type dft = (Type) getDepointFrom();
//		return dft == null ? primitive : dft;
//	}
	
	@Override
	public ArithmeticExpression getDepointFrom() {
		switch ((Operator) getOp()) {
		case Point:		return throwTodoException("Supplying a pointing chain cache?");
		case Depoint:	return (ArithmeticExpression) getFirstOperand();
		default:		
		}
		return throwTodoException("unsupported depointing-from");
	}
	
	@Override
	public PlatformType nextPointingType() {
		final ArithmeticExpression npt = nextPointing();
		return npt == null 
				? primitive 
				: PointerType.from((Pointer) npt);
	}
	
	@SuppressWarnings("deprecation")
	@Override
	public ArithmeticExpression getPointTo() {
		return get(()-> (ArithmeticExpression) nextPointingType(),
				e-> throwTodoException("pointing to non-pointer type", e));
	}
	
	public PlatformType getPointToEndType() {
		return primitive != null
				? primitive
				: ((PointerType) nextPointing()).getPointToEndType();
	}
	
	@Override
	public PlatformType getType() {
		return this;
		
		// Pointer has neither primitive nor constant type information
//		return primitive != null 
//				? primitive
//				: super.getType();
		
//		return pt == null || pt == NULL_POINTER_TYPE || pt.equals(DataType.Void)	
//				? (primitive == null ? NULL_POINTER_TYPE : primitive)
//				: pt;
	}

	@Override
	public java.lang.String getID(SerialFormat format) {
		if (equalsToCache(DataType.String)) return String.toZ3SmtType();
		
		java.lang.String npid = ((Operator) getOp()).getID(format);
		final ArithmeticExpression np = nextPointing();
		if (isNull()) 
			npid += "null";
		else if (np instanceof PointerType) 
			npid += ((PointerType) np).getID(format);
		else 
			npid += getPrimitive().getID(format);
		return npid;
	}
	
	public DataType getPrimitive() {
		return primitive;
	}

//	public Function getFunctionScope() {
//	if (primitive != null) return primitive.getFunctionScope();
//	return super.getFunctionScope();
//}

	/**
	 * @return null as the non-defined infinity
	 */
	@Override
	public Number<?> getPositiveInfinity() {
		return null;
	}
	
	/**
	 * @return null as the non-defined infinity
	 */
	@Override
	public Number<?> getNegativeInfinity() {
		return null;
	}
	
	
	
	@Override
	public Assignable<?> getAssignable() {
		return null;
	}
	
	@Override
	public Boolean isAssigned() {
		return false;
	}

	/* (non-Javadoc)
	 * @see ompca.vodcg.condition.data.Type#isNumeric()
	 */
	@Override
	public boolean isNumeric() {
		return false;
	}
	
	@Override
	public boolean isPrimitive() {
		return false;
	}

	/**
	 * Overriding since the {@link Expression} operands may be empty for a pointer type.
	 * 
	 * @see ompca.vodcg.condition.Relation#isEmpty()
	 */
	@Override
	public boolean isEmpty() {
		return primitive == null && super.isEmpty();
	}
	
	/**
	 * @return True if this is a {@link #NULL} pointer or 
	 * 	points to nothing (null).
	 */
	@Override
	public boolean isNull() {
		if (this == PointerType.NULL_POINTER_TYPE) return true;
		final ArithmeticExpression np = nextPointing();
		return np == null 
				? getPrimitive() == null
				: ((PointerType) np).isNull();
	}
	
	@Override
	public Boolean isZero() 			{return false;}
	@Override
	public Boolean isPositive() 		{return null;}
	@Override
	public Boolean isPositiveOrZero() 	{return null;}
	@Override
	public Boolean isPositiveInfinity() {return null;}
	@Override
	public Boolean isNegative() 		{return null;}
	@Override
	public Boolean isNegativeInfinity() {return null;}
	@Override
	public Boolean isLessThan(NumericExpression ne2) 	{return null;}
	@Override
	public Boolean isLessEqual(NumericExpression ne2) 	{return null;}
	
	@Override
	public boolean isInstance() {
		return false;
	}

	@Override
	protected Boolean cacheConstant() {
		return true;
	}
	
	@Override
	protected PointerType toConstantIf() {
		return this;
	}
	
	
	
	@Override
	protected List<Integer> hashCodeVars() {
		List<Integer> vars = new ArrayList<>(super.hashCodeVars());
		vars.add(primitive == null ? 0 : primitive.hashCode());
		return vars;
	}

	@Override
	protected boolean equalsToCache(SystemElement e2) {
		PointerType pt2 = (PointerType) e2;
		DataType ptp2 = pt2.primitive;
		return primitive == null 
				? ptp2 == null && super.equalsToCache(e2)
				: primitive.equals(ptp2);
	}
	
	@Override
	public Boolean equalsLogically(NumericExpression ne2) {
		return equalsToCache((SystemElement) ne2);
	}
	
	public boolean equalsPointTo(PointerType pt2) {
		if (this == pt2)				return true;
		if (pt2 == null)				return false;
		
		DataType ptp2 = pt2.getPrimitive();
		if (primitive != ptp2) 	return false;
		return super.equalsPointTo(pt2);
	}

	
	
	/**
	 * Either a {@link PointerType} or a {@link DataType} can be hosted 
	 * by this pointing type, where a {@link PointerType} is left for 
	 * {@link Pointer#pointTo(Expression)}.
	 * 
	 * @param type
	 */
	public void pointTo(PlatformType type) throws UnsupportedOperationException {
		if (isFinal()) throwTodoException("Immutable pointer type");
		
		if (type instanceof DataType) pointToPrimitive((DataType) type);
		else if (type instanceof Expression) pointTo((Expression) type);
		else throwTodoException("unsupported pointer");
	}
	
	/**
	 * For pointing to a non-pointer (primitive) type.
	 * 
	 * @param type
	 */
	public void pointToPrimitive(DataType type) {
		setPrimitive(type);
		if (nextPointing() != null) super.pointTo(null);
	}

	public void setPrimitive(DataType type) {
		if (type == null) throwNullArgumentException(
				"type. Null should be represented by pointer or void type explicitly");
		primitive = type;
		setDirty();
	}
	
	/**
	 * @param type - either a {@link PointerType} or a {@link DataType} to be hosted by 
	 * 	this de-pointing type.
	 */
	public void depointFrom(DataType type) {
		pointTo(type);
	}
	
	/**
	 * For a de-pointing instance.
	 * 
	 * @param addressable
	 */
	@Override
	public void depointFrom(Expression addressable) throws UnsupportedOperationException {
		if (addressable != null) throwTodoException("De-pointing meta-type!");
		super.depointFrom(addressable);
	}

//	@Override
//	public Type nextPointing() {
//		return (ArithmeticExpression) getFirstOperand();
//	}
	
	
	
	@Override
	public ArithmeticExpression add(ArithmeticExpression addend) 			{return null;}
	@Override
	public ArithmeticExpression subtract(ArithmeticExpression subtrahend) 	{return null;}
	@Override
	public ArithmeticExpression multiply(ArithmeticExpression multiplicand) {return null;}
	@Override
	public ArithmeticExpression divide(ArithmeticExpression divisor) 		{return null;}
	@Override
	public Expression negate() {return null;}
	@Override
	public Proposition lessThan(NumericExpression ne2) {return null;}
	@Override
	public Proposition lessEqual(NumericExpression ne2) {return null;}

	
	
	/**
	 * @return non-null type
	 */
	public ArrayType toArrayType() {
		final ArrayType a = ArrayType.from((PlatformType) this, null);
		final PlatformType npt = nextPointingType();
		if (npt instanceof DataType) 
			a.pointTo(npt);
		else if (npt instanceof PointerType) 
			a.pointTo((Expression) ((PointerType) npt).toArrayType());
		else
			throwTodoException("should have some pointing type");
		return a;
	}
	
	@Override
	public java.lang.String toNonEmptyString(boolean usesParenAlready) {
		if (this == PointerType.NULL) return "NULL";
		if (testsNonNull(()-> equals(DataType.String))) return String.toZ3SmtType();

		ArithmeticExpression np = nextPointing();
		final PlatformType npt = np == null ? getPrimitive() : np.getType();
		assert npt != null;
		java.lang.String pttStr = npt.toString(), 
				ptStr = np == null ? npt.toString() : np.toString();
		
		switch ((Operator) getOp()) {
		case Point:
			return (usesParenAlready ? "" : "(") + ptStr + " *" + (usesParenAlready ? "" : ")");
		case Depoint:
			return "& " + ptStr + " (Pointer -> " + pttStr + ")";
		default:
			assert (false);
			return null;
		}
	}

	
	
	static private final java.lang.String DPT_OP = Operator.Depoint.toZ3SmtString(null, false, false),
			SPT_OP = Operator.Point.toSingleZ3SmtString(),
			VT = DataType.Void.toZ3SmtString(false, false),	// void type
			PT = "PT",						// pointer-able type
			PPT = "(Pointer " + PT + ")";	// pointer of PT type
	
	/**
	 * Pointer function logic: 
	 * e.g. randlc(&tran, ...) -> tran = *x 
	 * 	-> depoint(tran) = x <-> tran = point(x)
	 *
	 * Defining pointer type via Z3 recursive data-type.
	 * 
	 * TODO? @param pointToType - null means declaring Pointer data type.
	 * @return
	 */
	static public java.lang.String toZ3SmtString() {
		VODCondGen.addKeyword(SerialFormat.Z3_SMT, 
				DPT_OP, SPT_OP, "Pointer", "point", PT, "PT_", "prim", "ptr", "addr", "is-ptr", "_v", "_p");
		return "(declare-datatypes (PT_) ((Pointer \n" + 
				"				" + SMT_NULL + "\n" + 
				"				" + VT + "\n" + 
				"				(prim (" + SPT_OP + " PT_))\n" + 
				"				(ptr (addr Pointer)))))\n" + 
				"(declare-sort " + PT + ")\n" + 
				"(declare-sort " + VT + ")\n" + 
				toZ3SmtPTFunction() +
				"(define-fun point ((_p " + PPT + ")) " + PPT + "\n" + 
				"				  (ite (is-ptr _p) (addr _p) _p) \n" + 
				") \n" + 
				"(declare-fun " + DPT_OP + " (" + PT + ") " + PPT + ")\n" + 
				"(declare-const _v PT)\n" + 
				"(declare-const _p " + PPT + ")\n" + 
				"(assert (iff (= (" + DPT_OP + " _v) _p) (= _v (" + SPT_OP + " _p))))\n" + 
				"";
	}
	
	@Override
	public java.lang.String toZ3SmtString(
			boolean printsVariableDeclaration, boolean printsFunctionDefinition) {
//		if (this == NULL_POINTER_TYPE) return SMT_NULL;
		if (testsNonNull(()-> equals(DataType.String))) return String.toZ3SmtType();

		final DataType prim = getPrimitive();
		final ArithmeticExpression np = nextPointing();
		if (np == null && !printsVariableDeclaration && !printsFunctionDefinition) {
			if (prim != null) return prim.toZ3SmtPointableTypeOperator();
		}
				
		final java.lang.String type = np == null
				? prim.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition)
				: getNonNull(()-> np.getType().toZ3SmtString(
				printsVariableDeclaration, printsFunctionDefinition));
		return printsVariableDeclaration
				? PPT
				/* TODO: "(Pointer " + type + ")"
				 * (PT != PT2) -> typeOf((Pointer PT)) = typeOf((Pointer PT2))
				 */
				: type;
	}

	static private java.lang.String toZ3SmtPTFunction() {
		return "(declare-fun pt2i (" + PPT + ") " + DataType.Int.toZ3SmtString(false, false) + ")\n" + 
				toZ3SmtPTFunction(DataType.Int) +
				toZ3SmtPTFunction(DataType.Real) +
				toZ3SmtPTFunction(DataType.Bool) +
				(Char.isUsed() ? toZ3SmtPTFunction(DataType.Char) : "");
//				toZ3SmtPTFunction(DataType.Void);
	}
	
	static private java.lang.String toZ3SmtPTFunction(DataType prim) {
		return "(declare-fun " + prim.toZ3SmtPointableTypeOperator() + 
				" (" + prim.toZ3SmtString(false, false) + ") " + PPT + ")\n"; 
	}

}