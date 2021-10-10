package ompca.vodcg.condition.data;

import java.util.List;

import ompca.vodcg.SystemElement;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.FunctionalPathVariable;
import ompca.vodcg.condition.PathVariable;
import ompca.vodcg.condition.Variable;
import ompca.vodcg.condition.Expression;
import ompca.vodcg.condition.version.VersionEnumerable;
import ompca.vodcg.condition.version.ThreadRole.ExtendedRole;

/**
 * @author Kao, Chen-yi
 *
 */
public class ArrayType extends PointerType {

	public static final ArrayType PRIMITIVE_ARRAY_TYPE = new ArrayType(true);
	
	
	
	/**
	 * Size depends on the memory size (statically or dynamically) allocated 
	 * and is initially set unknown.
	 */
	private ArithmeticExpression size = null;
	

	
//	private ArrayType() {
//		this(true); 
//	}
	
	/**
	 * An array pointer type constructor.
	 * An array type is always constant (in a global scope).
	 */
	private ArrayType(boolean isFinal) {
		super(isFinal);
	}
	
	/**
	 * @param type - the element type
	 * @param size
	 */
	private ArrayType(DataType type, ArithmeticExpression size) {
		super(type);
		setSize(size);
	}
	
	/**
	 * @param pt
	 * @param size	- maybe null
	 */
	private ArrayType(PointerType pt, ArithmeticExpression size) {
		super(pt); 
		setSize(size);
	}
	
	public static ArrayType from(FunctionalPathVariable v) {
		return from(v.getType(), null);
	}
	
//	public static ArrayType from(PlatformType eleType) {
//		return from(eleType, null);
//	}
	
	/**
	 * @param eleType - the element type
	 * @param size
	 * @return non-null array type with t-type elements and the index (argument) from 0 to size-1
	 */
	public static ArrayType from(PlatformType eleType, ArithmeticExpression size) {
		return eleType instanceof DataType 
				? new ArrayType((DataType) eleType, size) 
				: new ArrayType((PointerType) eleType, size);
//		ArrayType at = new ArrayType();
//		at.pointTo(t);
//		at.setSize(size);
//		return at;
	}
	
	/**
	 * Ex., <code>((int *)asn)[arg]</code> is in type {@link DataType#Int}.
	 * 
	 * @param address
	 * @param astArgs - each argument represents an index but not size
	 * @return
	 */
	public static PlatformType from(VersionEnumerable<? extends Variable> address, List<ArithmeticExpression> astArgs) {
		if (address == null) throwNullArgumentException("assignable");
		
		PlatformType t = address.getType();
		if (astArgs != null && !astArgs.isEmpty()) try {
			if (t instanceof PointerType) {			
				// array subscript type: a[...]
				if (t instanceof ArrayType) ((ArrayType) t).setDimension(astArgs.size());
//				((ArrayType) t).increaseDimension() 
//				((ArrayType) t).setDimension(args.size() + 1);	// TODO? future dimension index
				
				// functional or dereferencing array type: &a[...]
				for (@SuppressWarnings("unused") ArithmeticExpression arg : astArgs) 
					t = ((PointerType) t).nextPointingType();
				
			} 
//			else throwTodoException("unsupported array type");
//				? new ArrayType((DataType) t, arg)
//				: new ArrayType((PointerType) t, arg);
				
//			} else throwInvalidityException(
//					"unsupported array type: " + asn.getShortNameAddress() + args);
//					"impointable array: " + asn.getShortNameAddress() + "[" + arg + "]");
		} catch (Exception e) {
			throwTodoException(e);
		}
		return t;
	}
	
	/**
	 * @param address
	 * @param role
	 * @return an virtual array type with dimensions increased by the functional-lable <code>role</code>.
	 */
	public static PlatformType from(VersionEnumerable<? extends PathVariable> address, ExtendedRole role) {
		if (address == null) throwNullArgumentException("assignable");
		if (role == null) throwNullArgumentException("role");
		
		return from(address, role.getArguments());
	}
	
	
	
	public ArithmeticExpression getSize() {
		return size;
	}

	public void setSize(final ArithmeticExpression size) {
		if (isFinal()) throwTodoException("Immutable array type");

		this.size = size;
	}

	/**
	 * @param dim - dimension index
	 * @return
	 * @throws UnsupportedOperationException
	 */
	public ArrayType setDimension(int dim) throws UnsupportedOperationException {
		if (dim < 0) throwInvalidityException("negative dimension");
		if (isFinal()) throwTodoException("Immutable array type");
		
		final int oldDim = getDimension();
		try {
			if (oldDim < dim) 			// 0 -> oldDims -> dims
				return insertDimension().setDimension(dim-1);
			else if (oldDim > dim) 		// 0 -> dims -> oldDims
				return ((ArrayType) getPointTo()).setDimension(dim);
			
		} catch (ClassCastException e) {
			throwTodoException("Wrong array type: " + this);
		}
		return this;				// oldDims == dims
	}
	
	/**
	 * This is an immutable operation and producing new array types.
	 * 
	 * (a...[])[] = *(*...a)
	 *  
	 * @return
	 * @throws UnsupportedOperationException 
	 * 	- not only immutable but non-produce-able if this array type is final.
	 */
	public ArrayType increaseDimension() throws UnsupportedOperationException {
		if (isFinal()) throwTodoException("Immutable array type");
		ArrayType ida = new ArrayType(false);
		ida.pointTo((Expression) this);
		return ida;
	}
	
	/**
	 * @return
	 * @throws UnsupportedOperationException
	 */
	private ArrayType insertDimension() throws UnsupportedOperationException {
		return insertDimension(nextPointingType());
	}
	
	/**
	 * a(T [])...[] = *...*(*a)
	 *  
	 * @param dimType
	 * @return
	 * @throws UnsupportedOperationException
	 */
	private ArrayType insertDimension(PlatformType dimType) throws UnsupportedOperationException {
		if (dimType == null || isFinal()) throwTodoException("Immutable array type");
		
		ArrayType sub = from(dimType, null);
		sub.pointTo(nextPointingType());
		pointTo((Expression) sub);
		
		setDirty();
		return sub;
	}
	
	
	
	public boolean isVarargs() {
		return getSize() == null;
	}
	
	@Override
	protected boolean equalsToCache(SystemElement e2) 
	throws ClassCastException {
		if (e2 instanceof PointerType) 
			return size == null && super.equalsToCache(e2);
		
		final ArrayType a2 = (ArrayType) e2;
		final ArithmeticExpression size2 = a2.size;
		return (size == null ? size2 == null : size.equals(size2)) 
				&& super.equalsToCache(e2);
	}
	
	@Override
	protected List<Integer> hashCodeVars() {
		List<Integer> vars = super.hashCodeVars();
		vars.add(size == null ? 0 : size.hashCode());
		return vars;
	}
	

	
	private java.lang.String toZ3SmtDeclaration() {
		final PlatformType ptt = nextPointingType();
		return (size == null ? 
				"Int" : debugGet((SystemElement) null, ()-> size.getType().toZ3SmtString(false, false)))
				+ " " 
				+ (ptt instanceof ArrayType ? 
				((ArrayType) ptt).toZ3SmtDeclaration() : ptt.toZ3SmtString(false, false));
	}
	
	@Override
	public java.lang.String toZ3SmtString(
			boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs) {
		return "(Array " + toZ3SmtDeclaration() + ")";
	}
	
}