package ompca.vodcg.condition.data;

import java.util.Arrays;
import java.util.Collections;
import java.util.EnumMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.NavigableSet;
import java.util.Set;
import java.util.function.Supplier;

import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.Addressable;
import ompca.Mappable;
import ompca.condition.SerialFormat;
import ompca.vodcg.ASTAddressable;
import ompca.vodcg.ASTException;
import ompca.vodcg.Assignable;
import ompca.vodcg.SystemElement;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.AssignableExpression;
import ompca.vodcg.condition.Equality;
import ompca.vodcg.condition.Expression;
import ompca.vodcg.condition.PathVariable;
import ompca.vodcg.condition.PathVariablePlaceholder;
import ompca.vodcg.condition.Proposition;
import ompca.vodcg.condition.Referenceable;
import ompca.vodcg.condition.Relation;
import ompca.vodcg.condition.VariablePlaceholder;
import ompca.vodcg.condition.version.FunctionallableRole;
import ompca.vodcg.condition.version.NoSuchVersionException;
import ompca.vodcg.condition.version.ThreadRoleMatchable;
import ompca.vodcg.condition.version.Version;
import ompca.vodcg.condition.version.VersionEnumerable;

/**
 * A unification of pointing(*)/de-pointing(&) wrapper for 
 * directly mapping an AST pointer expression.
 * 
 * A unary {@link Relation} for pointing/de-pointing instances.
 * 
 * TODO: support multiple-variable pointing/de-pointing expression, 
 * 	i.e., &(a+b*c...) or *(a*b+c...), etc. 
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class Pointer 
extends Relation 
implements AssignableExpression, VersionEnumerable<PathVariable>	// TODO:, FunctionalRelation 
{ 

	public enum Operator implements Relation.Operator {
		/**
		 * A de-pointing operation is to resolve address of 
		 * the addressable stored in this pointer.
		 */
		Depoint {
			@Override
			public java.lang.String getID(SerialFormat format) {return "ref_";}
		},
		/**
		 * A pointing operation is to retrieve the data/type pointed to by 
		 * the addressable stored in this pointer.
		 */
		Point {
			@Override
			public java.lang.String getID(SerialFormat format) {return "pt_";}
		};
		
		public java.lang.String getID(SerialFormat format) {
			return throwTodoException("unsupprted op");
		}
		
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



		/* (non-Javadoc)
		 * @see ompca.vodcg.condition.Relation.Operator#negate()
		 */
		@Override
		public ompca.vodcg.condition.Relation.Operator negate() {
			switch (this) {
			case Depoint:	return Point;
			case Point:		return Depoint;
			default:		return null;
			}
		}
		
		public java.lang.String toString() {
			switch (this) {
			case Depoint:	return "&";
			case Point:		return "*";
			default:
				assert(false); return null;	// should NOT come here!
			}
		}
		
		public <H extends Relation> java.lang.String toZ3SmtString(
				H host, boolean printsVariableDeclaration, boolean printsFunctionDefinition) {
			switch (this) {
			case Depoint:	return "depoint";
			case Point:
				if (host instanceof Pointer) {
					if (((Pointer) host).isSingle()) return toSingleZ3SmtString();
				}
				throwTodoException("higher level pointer!");
			default:
				assert(false); return null;	// should NOT come here!
			}
		}
		
		/**
		 * @return Single pointer operator in Z3 SMT form.
		 */
		public java.lang.String toSingleZ3SmtString() {
			switch (this) {
			case Depoint:	return toZ3SmtString(null, false, false);
			case Point:		return "value";
			default:
				assert(false); return null;	// should NOT come here!
			}
		}
		
	}

	
	
	/**
	 * Representing all null pointers
	 */
	public static final Pointer NULL = new Pointer(Operator.Point);
	protected static final java.lang.String SMT_NULL = "NULL";
	
	/**
	 * Dimension depends on the pointing level and is initially set unknown.
	 */
	private int dim = -1;

//	/**
//	 * Representing either single operand of {@link Expression} for a pointer instance
//	 * or {@link DataType} for a pointer type.
//	 */
//	private Object addrOrType = null;
	
	

	protected Pointer(Operator op, Expression addressable, VODCondGen condGen, boolean isFinal) {
		super(op, Collections.singletonList(addressable), addressable.cacheRuntimeAddress(), condGen, isFinal);	// lazy scope setting
		
		resetDimension();
//		switch (op) {
//		case Depoint: 	depointFrom(addressable); break;
//		case Point: 	pointTo(addressable); break;
//		default: throwTodoException("unsupported pointer?");
//		}
	}

	protected Pointer(Operator op, Expression addressable, VODCondGen condGen) {
		this(op, addressable, condGen, false);
	}
	
	/**
	 * Non-final and non-constant-convenient constructor
	 * @param op
	 * @param isFinal
	 */
	protected Pointer(Operator op, final ASTAddressable rtAddr, boolean isFinal) {
		super(op, rtAddr, null, isFinal);
	}
	
	/**
	 * Final and constant-convenient constructor
	 * @param op
	 */
	protected Pointer(Operator op) {
		super(op, (VODCondGen) null);
	}
	
	/**
	 * Prefix ampersand operator parsing is pointing.
	 * 
	 * @param ampOperand - operand of a unary ampersand expression
	 * @param rtAddr 
	 * @param condGen
	 * @return
	 */
	public static Expression depointFromRecursively(
			IASTExpression ampOperand, final ASTAddressable rtAddr, VODCondGen condGen) {
		if (ampOperand == null) throwNullArgumentException("expression");
		
		return new Pointer(Operator.Depoint, 
				Expression.fromRecursively(ampOperand, rtAddr, condGen), 
				condGen);
	}
	
	/**
	 * Prefix star operator parsing is de-pointing.
	 * 
	 * @param starOperand - operand of a unary star expression
	 * @param condGen
	 * @return
	 */
	public static Expression pointFromRecursively(
			IASTExpression starOperand, final ASTAddressable rtAddr, VODCondGen condGen) {
		if (starOperand == null) return throwNullArgumentException("operand");
		
		final Expression e = Expression.fromRecursively(starOperand, rtAddr, condGen);
		if (e instanceof Pointer) {	
			final Pointer p = (Pointer) e;
			final ArithmeticExpression ep = p.getPointTo();
			if (ep instanceof Pointer) return (Pointer) ep;

		} else if (e instanceof NumericExpression) {
			/*
			 * ISO C 6.3.2.3 Pointers (under 6.3 Conversions) Paragraph 3:
			 * An integer constant expression with the value 0, or such an
			 * expression cast to type **`void *`**, is called a *null pointer
			 * constant*.
			 */
			if (tests(((NumericExpression) e).isZero())) return PointerType.NULL;
			
		} else if (e == null || e.isEmpty())
			throwTodoException("unsupported pointer");
			
		// including when e points to a non-integer primitive type
		return new Pointer(Operator.Point, e, condGen);
	}
	
	/**
	 * @param pvp - for some variable expression without star or ampersand syntax, but declared as pointer type.
	 * @return
	 */
	public static Pointer from(final PathVariablePlaceholder pvp) {
		if (pvp == null) return throwNullArgumentException("operand");
		return new Pointer(Operator.Point, pvp, pvp.getCondGen());
	}
	
//	public static Pointer Null(VOPCondGen condGen) {
//		if (NULL == null) NULL = new Pointer(condGen);
//		return NULL;
//	}
	
	

//	private static final Method METHOD_EXPRESSION_TRAVERSAL = 
//			getMethod(Pointer.class, "initiatesExpressionTraversal");
//	/* (non-Javadoc)
//	 * @see ompca.vodcg.condition.ArithmeticExpression#initiatesExpressionTraversal()
//	 */
//	@Override
//	public boolean initiatesExpressionComputation() {
//		return initiatesElementalTraversal(METHOD_EXPRESSION_TRAVERSAL);
//	}
//
//	/* (non-Javadoc)
//	 * @see ompca.vodcg.condition.ArithmeticExpression#initiateExpressionTraversal()
//	 */
//	@Override
//	public void initiateExpressionComputation() {
//		initiateElementalTraversal(METHOD_EXPRESSION_TRAVERSAL);
//	}
//
//	/* (non-Javadoc)
//	 * @see ompca.vodcg.condition.ArithmeticExpression#resetExpressionTraversal()
//	 */
//	@Override
//	public void resetExpressionComputation() {
//		resetElementalTraversal(METHOD_EXPRESSION_TRAVERSAL);
//	}
	

	
//	@Override
//	protected Expression cacheAssignerIf() {
//		return getNonNull(()-> getPointingBeginning())
//				.getAssigner();	
//	}

	@Override
	public void setAssigner(Expression rhs) {
		getBeginningPlaceholder().setAssigner(rhs);
	}

	@Override
	public void setAssigned(Boolean isAssigned) {
		getBeginningPlaceholder().setAssigned(isAssigned);
	}

	
	
	private void resetDimension() {
		ArithmeticExpression np = nextPointing();
		dim = np instanceof Pointer 
				? ((Pointer) np).getDimension() + 1 
				: 1;
	}

	/**
	 * @return the dimension of {@link #Array} or pointing level of {@link #Pointer} 
	 */
	public int getDimension() {
		if (dim == -1) resetDimension();
		return dim;
	}

	
	
	@Override
	public List<IASTStatement> getDependentLoops() {
		return getSkipNull(()-> getAssignable().getDependentLoops());
	}

	@SuppressWarnings("unchecked")
	public VariablePlaceholder<PathVariable> getBeginningPlaceholder() {
		final Expression pb = getPointingBeginning();
		if (pb instanceof VariablePlaceholder) try {
			return (VariablePlaceholder<PathVariable>) pb;
		} catch (ClassCastException e) {
			return throwTodoException(e);
		}
		if (pb instanceof Version) 
			return getNonNull(()-> ((Version<?>) pb).getAssignable()).getPathVariablePlaceholder();
		return throwTodoException("unsupported pointing beginning");
	}
	
	@Override
	public java.lang.String getID(SerialFormat format) {
//		if (format != null) switch (format) {
//		case Z3:
//			VOPCondGen.throwTodoException("pointer in Z3?");
//		case Z3_SMT:
//			return toZ3SmtString(false, false);
//		default:
//			break;
//		}
		
		java.lang.String npid = ((Operator) getOp()).getID(format);
		final ArithmeticExpression np = nextPointing();
		if (isNull()) npid += "null";
		else if (np instanceof Pointer) {
			final Pointer npt = (Pointer) np;
			npid += (npt.isNull() ? "null" : npt.getID(format));
		}
		else if (np instanceof Referenceable) npid += ((Referenceable) np).getID(format);
		else throwTodoException("unsupprted pointer");
		return npid;
	}

	@Override
	public Assignable<?> getAssignable() {
		return getBeginningPlaceholder().getAssignable();
	}
	
	@Override
	public IASTNode getASTAddress() {
		return getBeginningPlaceholder().getASTAddress();
	}

	@Override
	public java.lang.String getShortAddress() {
		return getBeginningPlaceholder().getShortAddress();
	}
	
	@Override
	public PathVariable getVersionSubject() {
		return getVariable();
	}
	
	@SuppressWarnings("unchecked")
	public <PV extends PathVariable> PV getVariable() {
		return (PV) getBeginningPlaceholder().getVariable();
	}
	
	/**
	 * Calculating type inductively:
	 * type(*v) = *type(v) = type(v).pointTo = nextPointingType.pointTo
	 * type(&v) = &type(v) = PointerType.from(v) = PointerType.from(nextPointing)
	 * 
	 * @return The type after evaluating this pointing expression.
	 * 	For example,
	 * 	Pointer (int) *v -> type(v) = int*, type(*v) = int
	 * 	Pointer (int*) &v -> type(v) = int, type(&v) = int*
	 * @see ompca.vodcg.condition.Expression#getType()
	 */
	@Override
	public PlatformType getType() {
		if (isNull()) return PointerType.NULL_POINTER_TYPE;

		switch ((Operator) getOp()) {
		case Point:
			/*
			 * Pointer (int) *v ->		type(v) = int*, type(*v) = int
			 * nextPointing(*v) = v ->	type(nextPointing(*v)) = int*, 
			 * 							type(*v) = nextPointing(int*) = nextPointing(type(v))
			 * 
			 * Pointer (int) v[] ->		type(v) = int*, type(v[]) = int
			 * nextPointing(v[]) = v ->	type(nextPointing(v[])) = int*, 
			 * 							type(v[]) = nextPointing(int*) = nextPointing(type(v))
			 */
			final Expression begin = getPointingBeginning();
			assert begin != null;
			ArithmeticExpression np = this;
			PlatformType t = begin.getType();
			while (np != begin) try {
				// np != begin => np instanceof Pointer && t instanceof PointerType
				assert np instanceof Pointer;
				final Pointer nptr = (Pointer) np;
				np = nptr.nextPointing();
	
				assert t instanceof PointerType;
				t = ((PointerType) t).nextPointingType();
				
			} catch (ClassCastException e) {
				throwTodoException(e);
			}
			return t;
			
		case Depoint:
			/*
			 * Pointer (int*) &v -> 	type(v) = int, type(&v) = int*
			 * nextPointing(&v) = v ->	type(nextPointing(&v)) = nextPointing(int*), 
			 * 							type(&v) = int* = pointerType(v) = pointerType(nextPointing(&v))
			 */
			return PointerType.from(nextPointing());
		default:		
		}
		
		return throwTodoException("unsupported pointer");
	}

	
	
	/**
	 * *v is pointed from v;
	 * &v is de-pointed from v;
	 * 
	 * @return
	 */
	public ArithmeticExpression getDepointFrom() {
		switch ((Operator) getOp()) {
		case Point:		return throwTodoException("Supplying a pointing chain cache?");
		case Depoint:	return (ArithmeticExpression) getFirstOperand();
		default:		
		}
		return throwTodoException("unsupprted depointing-from");
	}
	
	/**
	 * @return this with a wrapper.
	 * @see ompca.vodcg.condition.Relation#getPointers()
	 */
	@Override
	public Set<Pointer> getPointers() {
		Set<Pointer> ps = new HashSet<>();
		ps.add(this);
		return ps;
	}
	
	public ArithmeticExpression getPointTo() {
		if (getOp() == Operator.Point) throwTodoException("Supplying a pointing chain cache?");
		return (ArithmeticExpression) getFirstOperand();
	}
	
	public ArithmeticExpression getPointToEnd() {
		ArithmeticExpression pt = getPointTo(); 
		if (pt == null) 
			return null; 
		if (pt instanceof Pointer) 
			return ((Pointer) pt).getPointToEnd();
//		if (operand.getType() == DataType.Pointer)	// e.g. a pointer VariablePLaceholder 
//			return null;	// some memory value NOT in Expression type
		return pt; 
	}
	
//	public ArithmeticExpression getPointingEnd() {
//		return this;
//		switch ((Operator) getOp()) {
//		case Point:			return this;
//		case Depoint:		return getPointToEnd();
//		default:		
//		}
//		throwTodoException("unsupprted pointing-end");
//		return null;
//	}
	
	/**
	 * @return @NotNull beginning expression.
	 */
	public Expression getPointingBeginning() {
		if (isNull()) return this;
		
		final ArithmeticExpression np = nextPointing();
		assert np != null;
		if (np instanceof Pointer) 
			return ((Pointer) np).getPointingBeginning();
		if (np instanceof Expression) 
			return (Expression) np;
		
		return throwTodoException("unsupprted pointing-beginning");
	}
	
	public PointerType getPointerType() {
		return PointerType.from(this);
	}
	
	/**
	 * For a pointing instance.
	 * 
	 * @param addressable 
	 * 	- {@code null} is left for {@link PointerType#pointToPrimitive(DataType)}.
	 * @throws UnsupportedOperationException TODO
	 */
	public void pointTo(Expression addressable) throws UnsupportedOperationException {
		if (isFinal()) throwTodoException("truly final?");
		
		if (getOp() == Operator.Depoint) depointFrom(addressable);
		else setOnlyOperand(addressable);

		resetDimension();
	}
	
	/**
	 * @param addressable
	 * 	- {@code null} is left for {@link PointerType#pointToPrimitive(DataType)}.
	 * @throws UnsupportedOperationException TODO
	 */
	public void depointFrom(Expression addressable) throws UnsupportedOperationException {
		if (isFinal()) throwTodoException("truly final?");
		
		if (getOp() == Operator.Point) throwTodoException("Supplying a pointing chain cache?");
		else {
			setOnlyOperand(addressable);
			resetDimension();
		}
	}
	
	/**
	 * @return
	 * 	For example,
	 * 	Pointer (int) *v -> nextPointing is (int*) v
	 * 	Pointer (int*) &v -> nextPointing is (int) v
	 */
	public ArithmeticExpression nextPointing() {
		return (ArithmeticExpression) getFirstOperand();
	}
	
	public PlatformType nextPointingType() {
		final ArithmeticExpression np = nextPointing(); 
		if (np == null) return PointerType.NULL_POINTER_TYPE;
		if (np instanceof Pointer) return PointerType.from((Pointer) np);
		return np.getType();
	}
	


	/* (non-Javadoc)
	 * @see ompca.vodcg.condition.Expression#negate()
	 */
	@Override
	public Expression negate() throws UnsupportedOperationException {
		return get(()-> super.negate(),
				e-> AssignableExpression.super.negate());
//		return new Pointer((Operator) getOp().negate(), getFirstOperand(), getScopeManager());
	}

	@SuppressWarnings("unchecked")
	@Override
	public <T extends Addressable> T previous() {
		return (T) getBeginningPlaceholder().previous();
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public <T extends Addressable> NavigableSet<T> previousRuntimes() {
		return (NavigableSet<T>) getBeginningPlaceholder().previousRuntimes();
	}
	

	
	/**
	 * TODO? ID-equivalent hash code.
	 * 
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	protected List<Integer> hashCodeVars() {
//		return getID(null).hashCode();

		final ArithmeticExpression np = nextPointing();
		final Supplier<Integer> nphc = np == this
				? ()-> getPointingBeginning().hashCode()
				: ()-> np.hashCode();
		return Arrays.asList(
				get(nphc, ()-> 0),
				getDimension());
	}

	/**
	 * TODO? ID equivalence.
	 * 
	 * @see ompca.vodcg.condition.Relation#equals(java.lang.Object)
	 */
	@Override
	protected boolean equalsToCache(SystemElement e2) {
		final Pointer p2 = (Pointer) e2;
		final ArithmeticExpression np = nextPointing(), np2 = p2.nextPointing();
		if (np == null) return np2 == null;
		if (np2 == null) return np == null;
		if (!getType().equals(p2.getType())) return false;
		return equalsPointTo(p2);
//		return getID(null).equals(((Pointer) e2).getID(null));
	}

//	/**
//	 * @return non-null
//	 */
//	@Override
//	public Boolean equalsLogically(NumericExpression ne2) {
//		try {
//			return equalsToCache((SystemElement) ne2);
//		} catch (ClassCastException e) {
//			return false;
//		}
//	}
	
//	public boolean equalsPointTo(Expression e2) {
//		if (e2 instanceof Pointer) return equalsPointTo((Pointer) e2);
//		if (e2 instanceof Version<?>) return equalsPointTo((Version<?>) e2);
//		return false;
//	}
//	
//	public boolean equalsPointTo(Version<?> v) {
//		if (v == null) 								return false;
//		if (!(v.getType() instanceof PointerType))	return false;
//		return ;
//	}
	
	public boolean equalsPointTo(Pointer p2) {
		if (p2 == null)								return false;
		if (this == p2)								return true;
		
		if (getDimension() != p2.getDimension())	return false;
		
		ArithmeticExpression np = nextPointing(), np2 = p2.nextPointing();
		if (np == null) 							return np2 == null;
		else if (np instanceof Pointer)	
			return np2 instanceof Pointer && np.equals(np2);
		
//		Expression otherAorT = pointer2.getOnlyOperand();
//		if (operand == null) 			return otherAorT == null; 
//		//	operand instanceof VariableVersionDelegate
//		if (operand instanceof Expression) 
//			return ((Expression) operand).equals(otherAorT);
		return false;
	}

	@Override
	protected Boolean cacheGlobal() {
		return isNull() || !isInstance();
	}
	
	/**
	 * @return True if this is a {@link #NULL} pointer or points to nothing (null).
	 */
	public boolean isNull() {
		if (this == PointerType.NULL) return true;
		
		final ArithmeticExpression np = nextPointing();
		return np == null
				|| (np instanceof Number && ((Number<?>) np).isZero())
				|| (np instanceof Pointer && ((Pointer) np).isNull());
	}
	
	@Override
	public boolean isPrivate() {
		try {
			return getPointingBeginning().isPrivate();
			
		} catch (Exception e) {
			return SystemElement.throwTodoException(e);
		}
	}

	public boolean isSingle() {
		if (isNull()) return true;	// null pointer can be any-level pointer
		
		final ArithmeticExpression np = nextPointing();
		assert np != null;
		if (np instanceof Pointer) return false;
		
		final PlatformType ptt = np.getType();
		return !ptt.equals(DataType.Array) && !ptt.equals(DataType.Pointer);
	}
	
	/**
	 * @return True if this is a pointing/de-pointing instance (excluding {@link #NULL})
	 * 	rather than a pointing/de-pointing type.
	 */
	public boolean isInstance() {
		return true;
	}
	
	@Override
	public boolean isLikelyAssigned() {return !getType().isPrimitive();}

	
	
	/**
	 * @return true only possibly if it's type is primitive. 
	 */
	@Override
	public Boolean isZero() 
			throws ASTException {
		return getType().isNumeric()
				? getSkipNull(()-> AssignableExpression.super.isZero())
				: isNull();	// (*) NULL = (void *) 0
	}
	
	/**
	 * @return true only if the pointing end (value) is positive
	 */
	@Override
	public Boolean isPositive() {
		try {
			return getType().isNumeric()
					? getSkipNull(()-> AssignableExpression.super.isPositive())
					: true;	// pointer address is always a positive integer
					
		} catch (Exception e) {
			return throwTodoException(e);
		}
	}
	
	/**
	 * @return true only if the pointing end (value) is positive infinity
	 */
	@Override
	public Boolean isPositiveInfinity() {
		return getType().isNumeric()
				? getSkipNull(()-> AssignableExpression.super.isPositiveInfinity())
				: false; // pointer address is always a bounded positive integer
	}
	
	/**
	 * @return true only if the pointing end (value) is negative
	 */
	@Override
	public Boolean isNegative() {
		return getType().isNumeric()
				? getSkipNull(()-> AssignableExpression.super.isNegative())
				: false; // pointer address is always a positive integer
	}
	
	/**
	 * @return true only if the pointing end (value) is negative infinity
	 */
	@Override
	public Boolean isNegativeInfinity() {
		return getType().isNumeric()
				? getSkipNull(()-> AssignableExpression.super.isNegativeInfinity())
				: false; // pointer address is always a bounded positive integer
	}
	


//	/**
//	 * For Z3 native array logic support.
//	 * 
//	 * @return
//	 */
//	@Override
//	public boolean isZ3ArrayAccess() {
//		return getPointerType().isZ3ArrayAccess();
//	}

	
	
	protected Expression toConstantIf() {
		return isNull()
				? this		// PointerType.NULL
				: get(()->
				getPointingBeginning().toConstant(),
				e-> throwTodoException("unsupported constant", e)); 
	}


	
	/**
	 * @see ompca.vodcg.condition.Expression#toProposition()
	 */
	public Proposition toProposition() {
		if (nextPointingType() == DataType.Bool) 
			andSideEffect(()-> Equality.from(this, Proposition.PureTrue));	// non-reduction equality
		return super.toProposition();
	}
	
	
	
	/**
	 * Pointer type redirected description.
	 * 
	 * @see ompca.vodcg.condition.Relation#toNonEmptyString(boolean)
	 */
	protected java.lang.String toNonEmptyString(boolean usesParenAlready) {
		if (!isInstance()) return ((PointerType) this).toNonEmptyString(false);
		
		java.lang.String sic = toNonEmptyString();
		if (sic != null) return sic;
		
		final ArithmeticExpression pt = nextPointing();
		final java.lang.String ptStr = pt == null ? 
				"NULL" : pt.toString();
		switch ((Operator) getOp()) {
		case Point:
			return "*" + ptStr;	// *operand ::= value is pointed-to from operand
		case Depoint:
			return "&" + ptStr;	// &operand ::= value is pointing-to operand
		default:
			assert false;
			return null;
		}
	}

	
	
	/**
	 * @see ompca.vodcg.condition.Relation#toZ3SmtString(boolean, boolean, boolean)
	 */
	@Override
	public java.lang.String toZ3SmtString(
			boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs) {
		if (isInstance()) {
			if (isNull()) 
				return printsVariableDeclaration ? "" : SMT_NULL;
			if (printsVariableDeclaration) 
				throwTodoException("(declare-fun ?");
			
			final Operator op = getOp();
			final boolean isDepoint = op == Operator.Depoint;
			java.lang.String str = "(" 
					+ op.toZ3SmtString(this, false, printsFunctionDefinition) 
					+ " ";
			if (isDepoint) str += ("(" 
					+ ((DataType) getPointingBeginning().getType()).toZ3SmtPointableTypeOperator() 
					+ " ");   
			str += getID(SerialFormat.Z3_SMT);
			if (isDepoint) str += ")";
			return str + ")";
		}
		
		return ((PointerType) this).toZ3SmtString(
				printsVariableDeclaration, printsFunctionDefinition);
	}

	@Override
	public boolean isLoopIteratingIterator() {
		return throwTodoException("unsupprted operation");
	}

	@Override
	public boolean isLoopInitializedIterator() {
		return throwTodoException("unsupprted operation");
	}

	@SuppressWarnings("unchecked")
	@Override
	public Version<? extends PathVariable> getVersion() {
		return get(()-> getBeginningPlaceholder().getVersion(),
				()-> (Version<? extends PathVariable>) getPointingBeginning(),
				e-> null);
	}

	@Override
	public Version<? extends PathVariable> getVersion(FunctionallableRole role) {
		return get(()-> getBeginningPlaceholder().getVersion(role),
				()-> throwTodoException("unsupprted operation"));
	}

	@SuppressWarnings("unchecked")
	@Override
	public Version<? extends PathVariable> peekVersion() {
		return get(()-> getBeginningPlaceholder().peekVersion(),
				()-> (Version<? extends PathVariable>) getPointingBeginning(),
				e-> null);
	}

	@Override
	public Version<? extends PathVariable> peekVersion(ThreadRoleMatchable role) {
		return get(()-> getBeginningPlaceholder().peekVersion(role),
				()-> throwTodoException("unsupprted operation"));
	}

	@Override
	public boolean reversions() {
		return getBeginningPlaceholder().reversions();
	}

	@Override
	public void reversion(Version<? extends PathVariable> newVersion) throws NoSuchVersionException {
		getBeginningPlaceholder().reversion(newVersion);
	}

	@Override
	public void setVersion(Version<? extends PathVariable> newVersion) {
		getBeginningPlaceholder().setVersion(newVersion);
	}
	
}