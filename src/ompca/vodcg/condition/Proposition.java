package ompca.vodcg.condition;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.EnumMap;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTCaseStatement;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTDefaultStatement;
import org.eclipse.cdt.core.dom.ast.IASTDoStatement;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpressionStatement;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.core.dom.ast.IBinding;
import org.eclipse.cdt.core.dom.ast.IEnumeration;
import org.eclipse.cdt.core.dom.ast.IEnumerator;

import ompca.Addressable;
import ompca.DuoKeyMultiPartitionMap;
import ompca.DuoKeySetMultiPartitionMap;
import ompca.Elemental;
import ompca.Mappable;
import ompca.vodcg.ASTAddressable;
import ompca.vodcg.ASTException;
import ompca.vodcg.ASTLoopUtil;
import ompca.vodcg.ASTUtil;
import ompca.vodcg.Assignable;
import ompca.vodcg.Assignment;
import ompca.vodcg.SystemElement;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.FunctionCall.CallProposition;
import ompca.vodcg.condition.ReductionOperations.ReductionOctet;
import ompca.vodcg.condition.data.ArithmeticGuard;
import ompca.vodcg.condition.data.DataType;
import ompca.vodcg.condition.data.FiniteNumberGuard;
import ompca.vodcg.condition.version.Version;
import ompca.vodcg.parallel.OmpDirective;

/**
 * A Proposition can be regarded as a special Boolean Expression, 
 * which has a returned value of Boolean type.
 *  
 * Proposition 	::= ('let' Local (',' Local)* 'in')? 
 * 					(OrderRelation | And | Or | Imply | Not | TRUE | FALSE | FunctionCallProposition)
 * 
 * Local		::= Variable | Equality
 *  
 * And			::= Predicate (&& Predicate)*
 * Or			::= Predicate (|| Predicate)*
 * Imply	 	::= Predicate -> Predicate
 * Not			::= ~ Predicate
 * 
 * ALL propositional operations are default (if not specifically mentioned
 * or modifying its operator) to modify itself instead of creating new 
 * propositions to reduce system resource consumption.
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
abstract public class Proposition extends Relation implements SideEffectElement {
//implements Comparable<Proposition>, Comparator<Proposition> {

	public enum Operator implements Relation.Operator {
		And, Or, Imply, Not, Xor, Iff, True, False, FunctionCall;

		/* (non-Javadoc)
		 * @see ompca.vodcg.condition.Relation.Operator#isAssociativeTo(ompca.vodcg.condition.Relation.Operator)
		 */
		@Override
		public boolean isAssociativeTo(Relation.Operator op) {
			switch (this) {
			case And:			
			case Or:			
			case True:
			case False:
				return equals(op);
			case Xor:		// (F xor F) xor T = T, F xor (F xor T) = T, ...?
			case Iff:		// (A <-> B) <-> C	=	A <-> (B <-> C)?
			case Imply:		// (F -> T) -> F = F, F -> (T -> F) = T, ...
			case Not:			
			case FunctionCall:
			default:
			}
			return false;
		}

		@Override
		public boolean isCommutative() {
			switch (this) {
			case And:			
			case Or:			
			case Xor:		// F xor T = T xor F
			case Iff:		// A <-> B = A -> B && B -> A	=	B -> A && A -> B = B <-> A
			case True:
			case False:
				return true;
			case Imply:		// F -> T != T -> F
			case Not:			
			case FunctionCall:
			default:
				return false;
			}
		}
		
		@Override
		public Boolean isConstant() {
			switch (this) {
			case True:
			case False:
				return true;
			case And:			
			case Or:			
			case Xor:
			case Iff:
			case Imply:
			case Not:			
			case FunctionCall:
			default:
				return null;
			}
		}
		
		@Override
		public Boolean isUnary() {
			switch (this) {
			case Not:			
				return true;
			case And:			
			case Or:			
			case Xor:
			case Iff:
			case Imply:
			case True:
			case False:
			case FunctionCall:
			default:
				return false;
			}
		}
		
		public Boolean isBinary() {
			switch (this) {
			case Iff:
			case Imply:
				return true;
			case And:			
			case Or:			
			case Xor:
			case FunctionCall:
				return null;
			case Not:			
			case True:
			case False:
			default:
				return false;
			}
		}
		


		/* (non-Javadoc)
		 * @see ompca.vodcg.MultiPartitionable.Key#getPartitionMap()
		 */
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
			case Imply:			return Or;
			case And:
			case Or:
			case Not:
			case Xor:
			case FunctionCall:
			default:
				return null;	
			}
		}


		
		/**
		 * An infix serialization.
		 * 
		 * @see java.lang.Enum#toString()
		 */
		public String toString() {
			switch (this) {
			case And:			return "&&";
			case Or:			return "||";
			case Imply:			return "->";
			case Iff:			return "<->";
			case Not:			return "~";
			case Xor:			return "xor";
			case True:			return "T";
			case False:			return "F";
			case FunctionCall:	return "";	// in form [function-id]([args])
			default:
				assert(false); return null;	// should NOT come here!
			}
		}
		
		public <H extends Relation> String toZ3SmtString(
				H host, boolean printsVariableDeclaration, boolean printsFunctionDefinition) {
			switch (this) {
			case And:			return "and";
			case Or:			return "or";
			case Imply:			return "=>";
			case Not:			return "not";
			case Xor:			return "xor";
			case True:			return "true";
			case False:			return "false";
			case FunctionCall:	return "";	// leaving it for CallProposition.toZ3SmtString()
			default:
				assert(false); return null;	// should NOT come here!
			}
		}

	}

	
	
	protected static abstract class PropositionalConst extends Proposition {
		
		private String rule;
		private Relation.Operator rOp;
		
		protected PropositionalConst(
				Operator op, String rule, Relation.Operator reductionOp, Expression... reductionOperands) {
			super(op, Arrays.asList(reductionOperands));
			
			if (Elemental.testsNot(op.isConstant())) {
				if (reductionOperands == null) throwNullArgumentException("reduction");
				final int rSize = reductionOperands.length;
				if (tests(op.isUnary()) && rSize != 1) throwInvalidityException("non-unary reduction"); 
				if (tests(op.isBinary()) && rSize != 2) throwInvalidityException("non-binary reduction"); 
			}
			this.rule = rule;
			rOp = reductionOp;
		}
		
		public String getShortAddress() {
			for (Expression oprd : getOperands()) 
				if (oprd instanceof Addressable) return ((Addressable) oprd).getShortAddress();
			return "unknown-address";
		}
		
		@Override
		protected boolean equalsToCache(SystemElement e2) throws ClassCastException, NullPointerException {
			return getOp().equals(((Proposition) e2).getOp());
		}
		@Override
		protected List<Integer> hashCodeVars() {return Arrays.asList(getOp().hashCode());}
		
		@Override
		public boolean suitsSideEffect() {return false;}

		@Override
		protected Boolean cacheGlobal() {return true;}
		
		@Override
		protected Boolean cacheConstant() {return true;}
		@Override
		protected Expression toConstantIf() {return this;}

		@Override
		public String toZ3SmtString(boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs) {
			return getOp().toZ3SmtString(this, printsFunctionDefinition, printsFunctionDefinition)
					+ "\n;" + (rule != null ? rule : getShortAddress())
					+ "\t(reduce-from " + Relation.toZ3SmtString(
					rOp.toZ3SmtString(null, printsVariableDeclaration, printsFunctionDefinition), getOperands())
					.replaceAll("\\n", " ")
					+ ")" + "\n";
		}
		
	}
	
	
	
	public static final class True extends PropositionalConst {

		/**
		 * Singleton {@link True} and singleton {@link Operator#True}.
		 * @param reductionOperands 
		 * @param reductionOp 
		 */
		private True(String rule, Relation.Operator reductionOp, Expression... reductionOperands) {
			super(Operator.True, rule, reductionOp, reductionOperands);
		}
		
		public static True from(Relation.Operator reductionOp, Expression... reductionOperands) {
			return from(null, reductionOp, reductionOperands);
		}
		
		public static True from(String rule, Relation.Operator reductionOp, Expression... reductionOperands) {
			if (reductionOp == null) throwNullArgumentException("operator");
			return new True(rule, reductionOp, reductionOperands);
		}

		@Override
		protected Proposition andByReduce(Proposition p2)	{return p2;}
		@Override
		protected Proposition orByReduce(Proposition p2)	{return from(Operator.Or, this, p2);}
		@Override
		protected Proposition implyByReduce(Proposition p2)	{return p2;}	// T -> F = F
		@Override
		protected Proposition notByReduce() 				{return False.from(Operator.Not, this);}
		@Override
		protected Proposition iffByReduce(Proposition p2)	{
			return p2.isConstant() ? p2 : null;
		}
	}
	
	
	
	public static final class False extends PropositionalConst {

		/**
		 * Singleton {@link False} and singleton {@link Operator#False}.
		 * @param rule 
		 * @param reductionOperands 
		 * @param reductionOp 
		 */
		private False(String rule, Relation.Operator reductionOp, Expression... reductionOperands) {
			super(Operator.False, rule, reductionOp, reductionOperands);
		}
		
		public static False from(Relation.Operator reductionOp, Expression... reductionOperands) {
			return from(null, reductionOp, reductionOperands);
		}
		
		public static False from(String rule, Relation.Operator reductionOp, Expression... reductionOperands) {
			if (reductionOp == null) throwNullArgumentException("operator");
			return new False(rule, reductionOp, reductionOperands);
		}
		
		@Override
		protected Proposition andByReduce(Proposition p2)	{return from(Operator.And, this, p2);}
		@Override
		protected Proposition orByReduce(Proposition p2)	{return p2;}
		@Override
		protected Proposition implyByReduce(Proposition p2)	{return True.from(Operator.Imply, this, p2);}	// F -> A = T
		@Override
		protected Proposition notByReduce() 				{return True.from(Operator.Not, this);}
		@Override
		protected Proposition iffByReduce(Proposition p2)	{
			return p2.isConstant() ? p2.not() : null;
		}

	}
	

	
	private static final int PROP_CALL_DEPTH = 200;
	
	private final static Method METHOD_FROM = Elemental.getMethod(Proposition.class, 
			"from", Operator.class, Proposition.class, Supplier.class, Supplier.class);
	private final static Method METHOD_NOT = Elemental.getMethod(Proposition.class, 
			"not");
	
//	final static private Map<Set<Proposition>, Proposition> AndCache = new HashMap<>();
	final static private 
	DuoKeySetMultiPartitionMap<Proposition, Relation, Relation, Proposition> 
	AND_CACHE = new DuoKeySetMultiPartitionMap<>();
//	final static private Map<Set<Proposition>, Proposition> OrCache = new HashMap<>();
	final static private 
	DuoKeySetMultiPartitionMap<Proposition, Relation, Relation, Proposition> 
	OR_CACHE = new DuoKeySetMultiPartitionMap<>();
	final static private 
	DuoKeyMultiPartitionMap<Proposition, Proposition, Relation, Relation, Proposition> 
	IMPLY_CACHE = new DuoKeyMultiPartitionMap<>();
	final static private 
	DuoKeySetMultiPartitionMap<Proposition, Relation, Relation, Proposition> 
	IFF_CACHE = new DuoKeySetMultiPartitionMap<>();
	final static private Map<Operator, 
	DuoKeyMultiPartitionMap<Proposition, Proposition, Relation, Relation, Proposition>> 
	OPERATION_CACHE = new EnumMap<>(Operator.class);
	
	/**
	 * TODO: for all kinds of parent conditions
	 */
	final static private Map<IASTStatement, Proposition> 
	PC_PREFIX_CACHE = new HashMap<>();
	
	static public final Proposition PureTrue = True.from(Operator.True);
	static public final Proposition PureFalse = False.from(Operator.False);
	
	
	
	protected Set<Expression> locals = null;

	/**
	 * cache for logical not operation
	 */
	private Proposition not = null;				// cache for all propositions
	private List<Proposition> deMorgan = null;	// cache for And and Or
//	private Iterable<Proposition> props = null;
	
	
	
	/**
	 * Convenient constructor for unary propositions 
	 * such like {@link FiniteNumberGuard}.
	 *  
	 * @param operator - accepting {@link Relation.Operator} for {@link Predicate.Operator}
	 * 	since enum operators <em>can not</em> extend {@link Operator}.
	 * @param operand
	 */
	protected Proposition(Relation.Operator operator, Expression operand) {
		super(operator, operand);
//		initTrueAndFalse(leftOperand.getScopeManager());
	}
	
	/**
	 * Convenient constructor for ordered binary propositions 
	 * such like {@link OrderRelation} and {@link Imply}.
	 *  
	 * @param operator - accepting {@link Relation.Operator} for {@link Predicate.Operator}
	 * 	since enum operators <em>can not</em> extend {@link Operator}.
	 * @param leftOperand
	 * @param rightOperand
	 */
	protected Proposition(Relation.Operator operator, 
			Expression leftOperand, Expression rightOperand) {
		super(operator, leftOperand, rightOperand);
//	TODO: super(operator, operands, left_operand, right_operand, 
//				operands.scope \/ leftOperand.scope \/ rightOperand.scope);
//		initTrueAndFalse(leftOperand.getScopeManager());
	}
	
	/**
	 * Specific constructor for non-order propositions such like {@link Equality}.
	 *  
	 * @param operator - accepting {@link Relation.Operator} for {@link Predicate.Operator}
	 * 	since enum operators <em>can not</em> extend {@link Operator}.
	 * @param operands - should NOT be empty
	 * @param condGen 
	 */
	protected Proposition(Relation.Operator operator, Set<? extends Expression> operands, 
			VODCondGen condGen) {
		super(operator, operands, operands.iterator().next().cacheRuntimeAddress(), condGen);
//		initTrueAndFalse(condGen);
	}
	
//	TODO: protected Proposition(Relation.Operator operator, Set<Expression> operands) {
//		super(operator, operands, \/ operands.scope);
//	}

//	TODO: protected Proposition(
//			Relation.Operator operator, Collection<Proposition> operands, 
//			Proposition leftOperand, Proposition rightOperand) {
//		super(operator, operands, leftOperand, rightOperand, 
//				operands.scope \/ leftOperand.scope \/ rightOperand.scope);
//	}
	
//	TODO: protected Proposition(Relation.Operator operator, Collection<Proposition> operands, Proposition operand) {
//		super(operator, operands, operands.scope \/ operand.scope);
//		operands.add(operand);
//	}

	/**
	 * @param operator - accepting {@link Relation.Operator} for {@link Predicate.Operator}
	 * 	since enum operators <em>can not</em> extend {@link Operator}.
	 * @param operands - maybe empty for a constant {@link Operator#FunctionCall}
	 * @param condGen
	 */
	protected Proposition(Relation.Operator operator, 
			List<? extends Expression> operands, VODCondGen condGen) {
		super(operator, 
				operands, 
				condGen);
//		initTrueAndFalse(condGen);
	}
	
//	TODO: protected Proposition(Relation.Operator operator, Collection<Proposition> operands) {
//		super(operator, operands, \/ operands.scope);
//	}

	/**
	 * ONLY for the constant {@link True} and {@link False}.
	 */
	private Proposition(Operator op, List<? extends Expression> operands) {
		super(op, operands, null, (VODCondGen) null, true);
	}



//	/**
//	 * @param sm 
//	 * 
//	 */
//	private void initTrueAndFalse(VOPCondGen sm) {
//		TRUE = getTrue(sm);
//		FALSE = getFalse(sm);
//	}
	
	

	protected static Proposition from(Operator op, 
			Proposition p1, Supplier<Proposition> p2sp, Supplier<Proposition> constructor) {
		if (op == null) throwNullArgumentException("operator"); 
		if (p1 == null) throwNullArgumentException("p1"); 
		if (p2sp == null) throwNullArgumentException("p2 supplier"); 

		// delayed p2 computation
		if (p1.isTrue()) switch (op) {
		case And:							// T /\ A = A
		case Imply:							// T -> A = A
		case Iff:	return p2sp.get();		// T <-> A = T->A /\ A->T = A /\ T = A
		case Or:	return p1;				// T \/ A = T
			
		case False:
		case FunctionCall:
		case Not:
		case True:
		case Xor:
		default:
		}
		
		if (p1.isFalse()) switch (op) {
		case And:	return p1;				// F /\ A = F
		case Or:	return p2sp.get();		// F \/ A = A
		case Imply:	return True.from("F -> A = T", op, p1);
		case Iff:	return p2sp.get().not();			// F <-> A = F->A /\ A->F = T /\ ~A = ~A
		
		case False:
		case FunctionCall:
		case Not:
		case True:
		case Xor:
		default:
		}
		
//		// A /\ A = A
//		if (p1 == p2) return p1;	// structural reduce() is slow	
//		// A \/ A = A
//		if (p1 == p2) return p1;	// structural reduce() is slow	
//		// A -> A = T
//		if (p1 == p2) return TRUE;	// structural reduce() is slow	
//		
//		p1 = (Proposition) p1.reduce(); 
//		p2 = (Proposition) p2.reduce();
		Proposition p2 = p2sp.get();
		if (p2 == null) throwNullArgumentException("p2"); 
		if (p1.equals(p2)) switch (op) {	// reduce() after checking '==';
		case And:					// A /\ A = A
		case Or:	return p1; 		// A \/ A = A
		case Imply:	return True.from("A -> A = T", op, p1, p2);
		case Iff:	return True.from("A <-> A = T", op, p1, p2);

		case False:
		case FunctionCall:
		case Not:
		case True:
		case Xor:
		default:
		}
		
		if (OPERATION_CACHE.isEmpty()) {
			OPERATION_CACHE.put(Operator.And,	AND_CACHE);
			OPERATION_CACHE.put(Operator.Or,	OR_CACHE);
			OPERATION_CACHE.put(Operator.Imply,	IMPLY_CACHE);
			OPERATION_CACHE.put(Operator.Iff,	IFF_CACHE);
		}
		DuoKeyMultiPartitionMap<Proposition,Proposition,Relation,Relation,Proposition> 
		opCache = OPERATION_CACHE.get(op);
//		Proposition result = opCache.get(ps);
		Proposition result = opCache.get(p1, p2);

		// reducing dependency
		if (result == null) result = p1.reduceByOp(op, p2);

		if (result == null) {
			// checking for not-yet-reduced dependency
			p1.checkDependency(op, p2);
			// for and/or/iff -> setOnlyOperand(...)
//			if (op.isCommutative() && !p1.enters(METHOD_FROM) && !p2.enters(METHOD_FROM)) {	
//				p1.enter(METHOD_FROM); p2.enter(METHOD_FROM);
//				result = from(op, p2, ()-> p1, constructor);
//				p1.leave(METHOD_FROM); p2.leave(METHOD_FROM);
//			}
			
			// supposedly dependency free to avoid infinite recursion
			if (!p1.enters(METHOD_FROM, METHOD_NOT)) {
				p1.enter(METHOD_FROM);
				if (p1.not().equals(p2)) switch (op) {
				case And:	result = False.from("~A && A = F", op, p1, p2);		break;
				case Iff:	result = False.from("~A <-> A = F", op, p1, p2);	break;
				case Or:	result = True.from("~A || A = T", op, p1, p2);		break;
				case Imply:	result = p2; 										break;	// A -> ~A = ~A
				
				case False:
				case FunctionCall:
				case Not:
				case True:
				case Xor:
				default:
				}
				p1.leave(METHOD_FROM);
			}
		}
		if (result == null) result = constructor.get();
			
//		opCache.put(ps, result);	// caching the most reduced result at last
		opCache.put(p1, p2, result);
		return result;
//		return result.clone();
	}


	
	/**
	 * @param enumerator
	 * @param scopeManager 
	 * @return boolean constant following Java (TODO: C/C++) convention.
	 */
	public static Proposition from(IEnumerator enumerator) {
		return (enumerator != null
				&& (Boolean.parseBoolean(enumerator.getName())
						|| Boolean.parseBoolean(enumerator.toString()))) 
				? PureTrue : PureFalse;
	}
	
//	/**
//	 * @param stat
//	 * @param sideEffect
//	 * @param condGen 
//	 * @return
//	 */
//	public static Proposition fromRecursively(
//			IASTStatement stat, VOPConditions sideEffect, VOPCondGen condGen) {
//		if (stat == null) return null;
//		
//		if (stat instanceof IASTDeclarationStatement) {
//			final IASTDeclaration decl = 
//					((IASTDeclarationStatement) stat).getDeclaration();
//			if (decl instanceof IASTSimpleDeclaration) {
//				Proposition prop = null;
//				for (IASTDeclarator d : ((IASTSimpleDeclaration) decl).getDeclarators()) {
//					IASTInitializer di = d.getInitializer();
//					if (di != null && di instanceof IASTEqualsInitializer) {
//						Supplier<Proposition> dProp = ()-> fromRecursively(
//							(IASTNode)((IASTEqualsInitializer) di).getInitializerClause(), 
//							condGen);
//						prop = (prop == null) ? dProp.get() : prop.and(dProp);
//					} // TODO: else if ...
//				}
//				return prop;
//				
//			} // TODO: else if ...
//			
//		} else if (stat instanceof IASTExpressionStatement) {
//			return fromRecursively((IASTNode) 
//					((IASTExpressionStatement) stat).getExpression(), 
//					condGen);
//			
//		} // TODO: else if ...
//		
//		return null;
//	}
	
//	public static Proposition fromRecursively(Assignment asg, VODCondGen condGen) {
//		if (asg == null) throwNullArgumentException("assignment");
//		
//		return fromRecursively(asg.toASTNode(), condGen);
//	}
	
	public static Proposition fromRecursively(IASTNode node, final ASTAddressable rtAddr, VODCondGen condGen) 
			throws ASTException {
		if (node == null) throwNullArgumentException("node");

		return fromRecursivelyWithBranching(node, null, rtAddr, true, condGen);
	}
	
//	public static Proposition fromRecursively(IASTInitializerClause clause, 
//			VOPCondGen condGen) {
//		if (clause == null) return null;
//		
//		return fromRecursivelyWithBranching(clause, true, condGen);
//	}
	
	/**
	 * Possible sources for a proposition:
	 * 	1: Propositional clause -> 
	 * 	2: Expressional clause (e.toProposition + side-effect)
	 * 
	 * 		Expression.fromRecursively					Proposition.fromRecursively
	 * 						\										/
	 * 						Proposition.fromRecursivelyWithBranching
	 * 										|
	 * 						Proposition.fromParentBranchCondition
	 * 										|
	 * 						Proposition.fromRecursivelyWithoutBranching
	 * 										|
	 * 					Expression.fromRecursivelyWithoutTopProposition
	 * 					/											\
	 * 												sideEffect.fromRecursivelyWithBranching
	 * 																 |
	 * 												sideEffect.fromParentBranchCondition
	 * 																 |
	 * 												sideEffect.fromRecursivelyWithoutBranching
	 * 																 |
	 * 												Expression.toProposition.and(sideEffect)
	 * 																 |
	 * 
	 * 
	 * @param node - to be checked if it's a non-assignment, while implicitly an assignment 
	 * 	derives one top-level equality
	 * @param sideEffect - assignments may have side-effects to take care, while non-assignments 
	 * 	have NO side-effects to propagate outwards.
	 * @param concernsBranches
	 * @param condGen 
	 * @return
	 */
	private static Proposition fromRecursivelyWithBranching(
			IASTNode node, Assignment asm, ASTAddressable rtAddr, boolean concernsBranches, VODCondGen condGen) 
					throws ASTException {
		assert node != null;
		
		Proposition prop = null;
		
		// caching results for both {@link Expression}'s and {@link Proposition}'s
		Expression e = fromCache(node);
		if (e instanceof Proposition) return (Proposition) e;
		else if (e != null) return e.toProposition();	// returning sideEffect merged with e before
		
		else {
//			if (asm != null) rtAddr = asm.cacheRuntimeAddress();

			if (node instanceof IASTEqualsInitializer) prop = fromRecursively(
					// IASTDeclarator goes here to avoid re-parsing its initializer clause
					(IASTEqualsInitializer) node, rtAddr, condGen);
			else if (node instanceof IASTExpression) prop = fromRecursively(
					(IASTExpression) node, rtAddr, condGen);
			else if (node instanceof IASTExpressionStatement) prop = fromRecursively(
					((IASTExpressionStatement) node).getExpression(), rtAddr, condGen);
			else if (node instanceof IASTCompoundStatement) prop = fromRecursively(
					(IASTCompoundStatement) node, rtAddr, condGen);
			else if (node instanceof IASTForStatement) prop = Forall.from((IASTForStatement) node, rtAddr, condGen);
//			else returnTodoException("Assignment/non-expressional proposition?");
		
			if (concernsBranches) 
				prop = fromParentBranchCondition(node, prop, condGen);
			
			if (prop == null) {
				// default (not top priority) handler
				if (node instanceof IASTInitializerClause) {
					e = Expression.fromRecursively((IASTInitializerClause) node, rtAddr, condGen);
					if (e != null) prop = e.toProposition();

				} else returnTodoException("Unsupported node: " 
						+ ASTUtil.toStringOf(node) + " at " + ASTUtil.toLocationOf(node));
			} // else sideEffect has been set?
			
			if (prop != null) cache(node, prop);
			
		}// end of: e == null
		
		return prop;
	}
	
	
	
	private static Proposition fromRecursively(IASTEqualsInitializer init, final ASTAddressable rtAddr, VODCondGen condGen) {
		return Equality.from(init, rtAddr, condGen);
	}
	
	
	
	private static Proposition fromRecursively(IASTExpression exp, final ASTAddressable rtAddr, VODCondGen condGen) {
		assert exp != null;
		
		// boolean (binary) enum
		if (exp instanceof IASTIdExpression) return fromRecursively(
				(IASTIdExpression) exp);
		// Like IASTIdExpression, the parsing of IASTLiteralExpression has no side-effects.
		else if (exp instanceof IASTLiteralExpression) return fromRecursively(
				(IASTLiteralExpression) exp);
		else if (exp instanceof IASTUnaryExpression) return fromRecursively(
				(IASTUnaryExpression) exp, rtAddr, condGen);
		else if (exp instanceof IASTBinaryExpression) return fromRecursively(
				(IASTBinaryExpression) exp, rtAddr, condGen);
		else return throwTodoException("unsupported expression");
	}

	
	
	private static Proposition fromRecursively(IASTIdExpression exp) {
		IBinding idBind = ASTUtil.getNameOf(exp).resolveBinding();
		if (idBind instanceof IEnumerator) {
			IEnumerator idEnum = (IEnumerator) idBind;
			if (ASTUtil.isBinary((IEnumeration) idEnum.getType())) 
				return Proposition.from(idEnum);	// same as False.from(...)
		}
		return null;
	}
	

	
	private static Proposition fromRecursively(IASTLiteralExpression exp) {
		switch (exp.getKind()) {
		// True
		case IASTLiteralExpression.lk_true:		return PureTrue;
		// False
		case IASTLiteralExpression.lk_false:	return PureFalse;
		}
		return null;
	}
	
	
	
	private static Proposition fromRecursively(IASTUnaryExpression exp, final ASTAddressable rtAddr, VODCondGen condGen) {
		int unaryOp = exp.getOperator();
		IASTExpression unaryOprd = exp.getOperand();
		Expression eOprd = Expression.fromRecursively(unaryOprd, rtAddr, condGen);
		assert eOprd != null;
		
		switch (unaryOp) {
		// (): (clause)
		case IASTUnaryExpression.op_bracketedPrimary: 
		// Star: *clause
		case IASTUnaryExpression.op_star: 
			return eOprd.toProposition();
			
		// Not: !clause
		case IASTUnaryExpression.op_not: 
//			e.setSideEffect(prop);
			return eOprd.toProposition().not();
			
		default:
			// Subtraction assignment: clause--, --clause
			// Addition assignment: clause++, ++clause
			if (eOprd instanceof PathVariablePlaceholder) {
				final Proposition prop = Equality.from(
						unaryOp, (PathVariablePlaceholder) eOprd);
				if (prop != null) eOprd.andSideEffect(()-> prop);
				return prop;
			}
		}
		return returnTodoException("unsupported unary expression");
	}
	
	
	
	private static Proposition fromRecursively(
			IASTBinaryExpression exp, final ASTAddressable rtAddr, VODCondGen condGen) 
					throws ASTException {
		Expression lhs = Expression.fromRecursively(exp.getOperand1(), rtAddr, condGen), 
				rhs = Expression.fromRecursively(exp.getOperand2(), rtAddr, condGen);
		int binaryOp = exp.getOperator();
//		Function scope = Function.getFunctionScopeOf(binary, condGen);
		
		/* =, ==, /=, -=, %=, *=, +=, 
		 * TODO: &=?, TODO: |=?, TODO: ^=?, TODO: <<=?, TODO: >>=?,
		 * >=, >, <=, <, !=: TODO creating a NonEquality class with Set of operands
		 */
		Proposition prop = OrderRelation.fromRecursively(binaryOp, lhs, rhs);
		if (prop != null) return prop;
		
		Proposition lhsProp = lhs.toProposition();
		Supplier<Proposition> rhsProp = ()-> rhs.toProposition();
		switch (binaryOp) {
		// && 
		case IASTBinaryExpression.op_logicalAnd:	return lhsProp.and(rhsProp);
		// ||
		case IASTBinaryExpression.op_logicalOr:		return lhsProp.or(rhsProp);
		}
		return prop;
	}
	
	
	
	private static Proposition fromRecursively(IASTCompoundStatement compound, final ASTAddressable rtAddr, VODCondGen condGen) {
		assert compound != null;
		Proposition prop = null;
		for (IASTStatement stat : compound.getStatements()) {
			final Proposition statProp = fromRecursively(stat, rtAddr, condGen), prop_ = prop;
			if (statProp == null) throwNullArgumentException("statement proposition");
			prop = prop == null ? statProp : statProp.iff(()-> prop_);
		}
		return prop;
	}


	
	public static Proposition fromRecursivelyWithoutBranching(
			IASTInitializerClause clause, Assignment asm, VODCondGen condGen) 
					throws ASTException {
		if (clause == null) return null;
		
		return fromRecursivelyWithBranching(clause, asm, null, false, condGen);
	}
	

	
	public static Proposition fromParentBranchCondition(
			Assignable<?> descendant, Proposition descendantProp, VODCondGen condGen) 
					throws ASTException {
		if (descendant == null) throwNullArgumentException("descendant");
		
		for (IASTStatement b : descendant.getBranchScopes())
			if (descendant.isConditionalTo(b)) 
				return fromParentBranchCondition(b, descendant.getTopNode(), descendantProp, condGen);
		return descendantProp;
	}
	
	public static Proposition fromParentBranchCondition(
			IASTNode descendant, Proposition descendantProp, VODCondGen condGen) {
		if (descendant instanceof IASTName) return fromParentBranchCondition(
				Assignable.from((IASTName) descendant, descendantProp.cacheRuntimeAddress(), condGen), descendantProp, condGen);
		else {
			final IASTStatement parent = ASTUtil.getParentBranchOf(descendant);
			return parent == null 
					? descendantProp 
					: fromParentBranchCondition(parent, descendant, descendantProp, condGen);
		}
	}
	
	/**
	 * Considering branching-related statements with bypassing IASTExpressionStatement 
	 * and initializer (list).
	 * 
	 * ONLY a statement or top expression (with direct parent of branch type 
	 * statement) has to consider its grand-parent branch.
	 * 
	 * Finding {@code descendant}'s parent statement first, then {@code parent}'s grand one.
	 * 
	 * @param parent
	 * @param descendant
	 * @param descendantProp
	 * @param condGen
	 * @return
	 */
	public static Proposition fromParentBranchCondition(
			IASTNode parent, IASTNode descendant, 
			Proposition descendantProp, VODCondGen condGen) 
					throws ASTException {
		if (parent == null || descendant == null) return descendantProp;

		if (parent instanceof IASTStatement) return fromParentBranchCondition(
				(IASTStatement) parent, descendant, descendantProp, condGen);
		
		// descendant is part of parent branch (e.g. iteration bounds, etc.) and considering its grand-parent branch
		if (descendant == parent) return fromParentBranchCondition(
				descendant.getParent(), descendantProp, condGen);

		return fromParentBranchCondition(
				parent.getParent(), descendant, descendantProp, condGen);

//		List<IASTNode> parBranches = ASTUtil.getAncestorsOfUntil(
//				node.getParent(), ASTUtil.AST_BRANCH_TYPES);
//		if (parBranches == null) return nodeProp;
//		int pbSize = parBranches.size();
//		if (pbSize == 0) return nodeProp;
//		
//		// statBranch of the top branch statement is always IASTTranslationUnit
//		IASTNode parBranch = parBranches.get(pbSize - 1);
	}
	
	private static Proposition fromParentBranchCondition(
			IASTStatement parent, IASTNode descendant, 
			Proposition descendantProp, VODCondGen condGen) 
					throws ASTException {
		assert parent != null && descendant != null;
		
		Proposition result = null;
		if (parent instanceof IASTCaseStatement) result = fromParentSwitchCondition(
				(IASTCaseStatement) parent, descendantProp, condGen);
		else if (parent instanceof IASTDefaultStatement) result = fromParentSwitchCondition(
				(IASTDefaultStatement) parent, descendantProp, condGen);
		else if (parent instanceof IASTDoStatement) result = fromParentDoCondition(
				(IASTDoStatement) parent, descendantProp, condGen);
		else if (parent instanceof IASTForStatement) result = fromParentForCondition(
				(IASTForStatement) parent, descendantProp, condGen);
		else if (parent instanceof IASTWhileStatement) result = fromParentWhileCondition(
				(IASTWhileStatement) parent, descendantProp, condGen);
		else if (parent instanceof IASTIfStatement) result = fromParentIfCondition(
				(IASTIfStatement) parent, descendant, descendantProp, condGen);
		
		if (result != null) {
			if (!result.isFalse()) {
				assert parent instanceof IASTStatement;
				final IASTStatement parent_ = parent;
				result.addOmpSideEffect(()-> OmpDirective.from(parent_, condGen));
//				result.addSideEffect(PathCondition.from(result)); // result is returned as part of path condition
			}
			return result;
		}

		return fromParentBranchCondition(
				parent.getParent(), descendant, descendantProp, condGen);
	}
	
	/**
	 * @param stat
	 * @param statProp
	 * @param condGen
	 * @return
	 */
	private static Proposition fromParentSwitchCondition(IASTCaseStatement stat, 
			Proposition statProp, VODCondGen condGen) {
		IASTExpression condCase = stat.getExpression();
//		if (ASTUtil.hasAncestorAs(node, condCase, parBranches))	// bypassing condition's children 
//			return fromParentBranchCondition(statCase, branchProp, condGen);
//		else 
		return Equality.from(
				ASTUtil.getEnclosingSwitchStatementOf(stat).getControllerExpression(),
				condCase,
				statProp.cacheRuntimeAddress(), 
				condGen);
	}
		
	private static Proposition fromParentSwitchCondition(IASTDefaultStatement stat, 
			Proposition statProp, VODCondGen condGen) {
		IASTSwitchStatement statSwitch = ASTUtil.getEnclosingSwitchStatementOf(stat);
		Iterable<IASTCaseStatement> statCases = ASTUtil.getDescendantsOfAs(
				statSwitch, IASTCaseStatement.class);
		if (statCases != null) {
//			Or cases = new Or(
//					Function.getFunctionScopeOf(statSwitch, condGen), condGen);
			Proposition cases = null;
			for (IASTCaseStatement statCase : statCases) {
				Supplier<Proposition> acase = ()-> fromRecursively(
						(IASTNode) statCase.getExpression(), statProp.cacheRuntimeAddress(), condGen);
				cases = cases == null ? acase.get() : cases.or(acase);
			}
			return cases.not();
		}
		return statProp;
	}
		
	private static Proposition fromParentDoCondition(IASTDoStatement stat, 
			Proposition statProp, VODCondGen condGen) {
		IASTExpression cond = stat.getCondition();
//		if (ASTUtil.hasAncestorAs(node, cond, parBranches))	// bypassing condition's children 
//			return fromParentBranchCondition(statDo, branchProp, condGen);
//		else 
		return fromRecursively((IASTNode) cond, statProp.cacheRuntimeAddress(), condGen);
	}
		
	/**
	 * In an indirectly dependent loop, for example, 
	 * <code>for (it = 1; it <= NITER; it++) ... zeta = SHIFT + 1.0 / norm_temp1;</code>,
	 * <code>for (j = 0; j < lastcol - firstcol + 1; j++) ... norm_temp1 = norm_temp1 + x[j]*z[j];</code> and
	 * <code>conj_grad(colidx, rowstr, x, z, a, p, q, r, &rnorm);</code> 
	 * becomes 
	 * <code>zeta = SHIFT + 1.0 / norm_temp1(lastcol - firstcol + 1)</code> 
	 * /\ <code>forall (0 <= j < lastcol - firstcol + 1) ... norm_temp1(j) = norm_temp1(j-1) + x(j)*z(j)</code>
	 * /\ <code>conj_grad(colidx, rowstr, x, z, a, p, q, r, &rnorm)</code> 
	 * in cg.c 
	 * 
	 * For example an array in a dependent loop, such as frct[k][j][i][0] = frct[k][j][i][0] + ... 
	 * in for(...;i++), becomes frct(k,j,i,0) = frct(k,j,i-1,0) + ...
	 * 
	 * @param stat
	 * @param statProp
	 * @param condGen
	 * @return
	 */
	@SuppressWarnings("unchecked")
	private static Proposition fromParentForCondition(final IASTForStatement stat, 
			Proposition statProp, VODCondGen condGen) {
		if (!ASTLoopUtil.isCanonical(stat, condGen)) returnTodoException("non-canonical loop?");
		
		/* TODO: a. If E� inside independent-constant-iterated (possibly nested) loop(s) 
		 * 	L_Const : i. PathCond �= conditioning E with versioning OV by indices
		 */
//	if (ASTUtil.isConstant(loop)) 
//		pathBeginCond.and(generateConstLoopRewritingConditionsOfFrom(ovRef, exp, loop));
		
		/*	b. else if E� inside independent-variable-iterated (possibly nested) loop(s) 
		 * 	L_IV :
		 * 		i. PathCond �= functional versioning OV by inserting init. clos. and 
		 * 			postconditions
		 * 		ii. if OV is global, PathCond �= inserting versions with tag F
		 */
//	else {
		/*	d. (default loop-dependent rewritable) else if E� inside elsewhere (including
		 * 	that OV is an array inside dependent loops) :
		 */
		// excluding loop iterator increment
//		boolean isAsgNotInc = ovAsgners.size() > 1;
//		if (it != null && isAsgNotInc) {
//			for (Assignable ovrAsgner : ovAsgners) {
//				isAsgNotInc &= !ovrAsgner.equalsVariable(it);	
//				if (!isAsgNotInc) break;
//			}
//			if (isAsgNotInc) {
//			}
//		}
//	}
		
		/* for: initIf /\ condIf /\ prop  
		 */
		final Proposition itRange = ExpressionRange.fromIteratorOf(
				stat, statProp == null ? null : statProp.cacheRuntimeAddress(), condGen);
		if (statProp == null) statProp = itRange; 

		// for non-functional-ized yet statProp
		// iterator is assigned later than the initialized one
		else try {
			if (tests(statProp.dependsOn(
					PathVariablePlaceholder.fromCanonicalIteratorOf(stat, statProp.cacheRuntimeAddress(), condGen))) 
				&& !statProp.getOp().equals(Predicate.Operator.Forall)) 
				statProp = Forall.from(
						Arrays.asList((ExpressionRange<VariablePlaceholder<?>>) itRange), statProp); 
			
		} catch (ClassCastException e) {
			if (itRange instanceof Equality) statProp = itRange.and(statProp);	// constant canonical loop
			else returnTodoException("non-canonical loops?"); 
		} catch (Exception e) {
			throwUnhandledException(e);
		}
			
//		FunctionalVersion ver = FunctionalVersion.from(loop, condGen);
//		if (!statProp.dependsOn(ver)) {	
//			ver.checkUbiquitous();
//		}
		
		/*	TODO: c. else if E� inside other independently non-counter-iterated (possibly 
		 * 	nested) loop(s) L_NI :
		 * 		i.	PathCond �= functional versioning OV by inserting init. clos. and 
		 * 			postconditions of counting indices (CI) implied with general loop break 
		 * 			conditions, i.e. CI > variant_bound -> BreakCond 
		 * 		ii.	if OV is global, PathCond �= inserting versions with tag F
		 */
		return fromParentBranchCondition(stat, statProp, condGen);
	}
		
	/**
	 * <em>While</em> statement path condition: {@code statProp -> condProp} 
	 * @param stat
	 * @param statProp
	 * @param condGen
	 * @return
	 */
	private static Proposition fromParentWhileCondition(final IASTWhileStatement stat, 
			Proposition statProp, VODCondGen condGen) {
		assert stat != null;
		
		final Proposition condProp = fromRecursivelyWithoutBranching(stat.getCondition(), null, condGen);
//		if (ASTUtil.hasAncestorAs(node, cond, parBranches))	// bypassing condition's children 
//			return fromParentBranchCondition(statWhile, branchProp, condGen);
//		else 
		return fromParentBranchCondition(
				stat, 
				statProp != null ? statProp.imply(()-> condProp) : condProp, 
				condGen);
	}
	
	/**<pre>
	 * For example:
	 * ...
	 * if (NA == 1400 && NONZER == 7 && NITER == 15 && SHIFT == 10) {				// propIf = F
	 *     Class = 'S';
	 *     ...
	 * } else if (NA == 150000 && NONZER == 15 && NITER == 75 && SHIFT == 110) {	// propIf = T
	 *     Class = 'C';
	 *     ...
	 * }
	 * 
	 * case same-to-parent:
	 * 	if (parentIf) descendant: {
	 * 		...	descendantProp ...	=>	pic = propParentIf /\ descendantProp
	 * 	}								
	 * 
	 * case else-to-parent:
	 * 	if (parentIf) 
	 * 	else descendant: {
	 * 		...	descendantProp ...	=>	pic = ~propParentIf /\ descendantProp
	 * 	}								
	 * 
	 * @param parentIf
	 * @param descendant
	 * @param descendantProp
	 * @param condGen
	 * @return
	 */
	private static Proposition fromParentIfCondition(
			final IASTIfStatement parentIf, final IASTNode descendant, 
			final Proposition descendantProp, final VODCondGen condGen) 
					throws ASTException {
		assert parentIf != null;
		
		// picPrefix is bound to IASTIfStatement, but not then-/else-statement
//		PC_PREFIX_CACHE.clear();
		final boolean isElse = ASTUtil.isElseTo(descendant, parentIf);
		final IASTStatement parent = isElse ? parentIf.getElseClause() : parentIf;
		Proposition picPrefix = PC_PREFIX_CACHE.get(parent);
		
		if (picPrefix == null && !PC_PREFIX_CACHE.containsKey(parent)) {
			final Proposition propParentIf = fromIfCondition(parentIf, condGen);
			if (propParentIf == null) throwTodoException("truly null condition");
			
			/* case same-to-parent:
			 * 	if (parentIf) descendant: {
			 * 		...	descendantProp ...	=>	pic = propParentIf /\ descendantProp 
			 * 	}
			 * =>								
			 * 	if (picPrefix) if (parentIf) descendant: {
			 * 		...	propParentIf ...	=>	pic = picPrefix /\ propParentIf /\ descendantProp
			 * 	}			
			 */
			picPrefix = fromParentBranchCondition(
					parentIf.getParent(), parentIf, propParentIf, condGen); 
			if (picPrefix == null) throwTodoException("truly null condition");

			if (picPrefix.isTrue()) IfElseRule: {
				// propParentIf = T is in then
				IASTStatement elseStat = parentIf.getElseClause();
				// propParentIf = T is in the current else
				if (isElse) {
					if (elseStat instanceof IASTIfStatement) 
						elseStat = ((IASTIfStatement) elseStat).getElseClause();
					else break IfElseRule;
				}
				while (elseStat != null) {
					PC_PREFIX_CACHE.put(elseStat, False.from("If-else rule", Operator.Not, picPrefix));
					if (elseStat instanceof IASTIfStatement) 
						elseStat = ((IASTIfStatement) elseStat).getElseClause();
					else break;
				}
			} 
			
			// isElse produces falsely true if not checking mutex 
			if (isElse) picPrefix = picPrefix.isFalse() 
					&& !isMutexTrue(parent, condGen)
					/* case constant:
					 * 	if (true) ...
					 * 	else if (false) ...
					 * 	else descendant: {
					 * 		...	descendantProp ...	=>	pic = false
					 * 	}
					 */								
					? picPrefix
					/* case else-to-parent:
					 * 	if (parentIf) 
					 * 	else descendant: {
					 * 		...	descendantProp ...	=>	pic = ~propParentIf /\ descendantProp
					 * 										= ~picPrefix /\ descendantProp
					 * 	}
					 */								
					: picPrefix.not();
			
			PC_PREFIX_CACHE.put(parent, picPrefix);
		}
		return descendantProp == null ? picPrefix : picPrefix.and(()-> descendantProp);
				
//		if (ASTUtil.isElse(stat)) {
//			assert propParBranch != null;
//			Proposition propNotPar = propParBranch.not();
//			picPrefix = statIsIf 
//					/* case else: if-statement
//					 * 	if (condParBranch) ...
//					 * 	else if (condIf) ...	=>	preCond = ~condParBranch && condIf
//					 * 									pic = ~propParBranch /\ propIf /\ nodeProp
//					 * TODO: partially tested if, condParBranch == T => condIf is never tested
//					 */
//					? propNotPar.and(propIf)
//			
//					/* case else: other-statement
//					 * 	if (condParBranch) ...
//					 * 	else ...				=>	preCond = ~condParBranch
//					 * 									pic = ~propParBranch /\ nodeProp
//					 */
//					: propNotPar;
//				
//		} else {
//			/* (condParBranch) {
//			 * 	...			
//			 * 	if (condIf) ...		=>	preCond = condParBranch /\ condIf
//			 * 	...							pic = propParBranch /\ propIf /\ statProp
//			 * }
//			 */
//			if (statIsIf) picPrefix = 
//					propParBranch == null ? propIf : propParBranch.and(propIf);
//			
//			/* (condParBranch) {
//			 * 	...					=>	preCond = condParBranch
//			 * }							pic = condParBranch /\ statProp
//			 */
//			else if (propParBranch != null) picPrefix = propParBranch;
//			
//			/* =>	preCond = <no branches>
//			 * 		pic = statProp
//			 */
//		}
	}
	
	private static Proposition fromIfCondition(
			final IASTIfStatement parentIf, final VODCondGen condGen) 
					throws ASTException {
		assert parentIf != null;
		return fromRecursivelyWithoutBranching(
				parentIf.getConditionExpression(), null, condGen);
	}

		
	
	static protected <T> Collection<T> add(Collection<T> col, T ele) {
		addSkipException(col, ele);
		return col;
	}
	

	
	/**
	 * Default logical existing side-effect:
	 * SE = (P1 && P1.SE) op (P2 && P2.SE) op ... op (Pn && Pn.SE)
	 */
	@Override
	protected <OT extends Expression> boolean cacheOperandDirectSideEffect(
			final OT oprd) {
		if (oprd == null) throwNullArgumentException("operand");
		if (!oprd.suitsSideEffect()) return true;
		
		final Relation.Operator op = getOp();
		if (!(op instanceof Operator)) throwTodoException("unsupported operator");
		
		switch ((Operator) op) {
		case And:
		case True:	// SE = P1.SE && P2.SE && ... && Pn.SE
			andSideEffect(()-> oprd.getSideEffect());
			break;
			
		case Or:	// SE = P1.SE || P2.SE || ... || Pn.SE
			orSideEffect(()-> oprd.getSideEffect());
			break;
			
		case False:
			returnTodoException("False && False.SE?");
			break;
			
		case Not:
//			return ((Not) this).cacheOperandDirectSideEffect(parentSe, oprd);
		case Imply:
//			return ((Imply) this).cacheOperandDirectSideEffect(parentSe, oprd);
		case FunctionCall:
//			return ((FunctionCall<?>.CallProposition) this).cacheOperandDirectSideEffect(parentSe, oprd);
			returnTodoException("unwrapped proposition");
		case Iff:
		case Xor:
		default:
			returnTodoException("unsupported side-effect logics");
//			parentSe.add(op, oprd.getSideEffect().and(()-> prop));
			break;
		}
		return true;
	}
	
	protected <OT extends Expression> boolean cacheExpressionalOperandDirectSideEffect(OT oprd) {
		return super.cacheOperandDirectSideEffect(oprd);
	}
	

	
	/**
	 * @return A non-null read-only proposition set for proposition data safety.
	 */
	@SuppressWarnings("unchecked")
	public Iterable<Proposition> getPropositions() {
		final Collection<? extends Expression> operands = getOperands();
		if (operands.isEmpty()) return Collections.singleton(this);
		
		for (Expression e : operands) 
			if (!(e instanceof Proposition)) 
				return Collections.singleton(this);
//			operands.removeIf(e -> !(e instanceof Proposition));
//			Debug.throwTodoException("Non-propositional operands!");
	
		return (Iterable<Proposition>) operands;
	}
	
	
	
	@Override
	public Boolean dependsOn(Expression e) {
		if (locals != null) for (Expression local : locals) {
			boolean depends = false;
			if (local instanceof Version<?>) 
				depends = ((Version<?>) local).getSubject().equals(e);
			if (local instanceof Equality) 
				depends = ((Equality) local).dependsOn(e);
			if (depends) return true;
		}
		return super.dependsOn(e);
	}
	
	public boolean isTrue() {
		return getOp().equals(Operator.True);
	}
	
	public boolean isFalse() {
		return getOp().equals(Operator.False);
	}
	
	

	final public Proposition and(final Proposition p2) {
		return and(()-> p2);
	}
	
	final public Proposition and(final Supplier<Proposition> p2) {
//		return And.from(this, p2);
		return debugGet(100, ()-> And.from(this, p2));
	}
	
	/**
	 * Guard flattening method for any pre-/post-processing.
	 * Linearization during optimization saves hashing time.
	 * 
	 * @param p2s
	 * @return
	 */
	final public Proposition and(List<Proposition> p2s) {
		return and(()-> And.from(p2s));
	}
	
//	final public Proposition and(Set<Proposition> p2s) {
//		if (p2s == null || p2s.isEmpty()) {
//			Debug.throwInvalidityException("Empty p2's?");
//			return null; 
//		}
//		return and(new ArrayList<>(p2s));
//	}
	
	final public Proposition andSkipNull(final Proposition p2) {
		return p2 == null ? this : and(()-> p2);
	}
	
	/**<pre>
	 * For general (the last) Proposition/Predicate sub-type and handling.
	 * 
	 * Guard for any pre-/post-processing:
	 * 
	 * (II)
	 * (i)
	 * b1 R a /\ a R b2
	 * = b1 R a R b2
	 * 
	 * (ii) 							(b1 -> a) /\ (b2 -> a) /\ (b1 -> b2) 
	 * b1 R a /\ b2 R a /\ b1 R b2		b1 b2 a | b1->a | b2->a | b1->b2 | ./\./\.
	 * = b1 R b2 R a					 0  0 0 |   1   |   1   |   1    |    1
	 * = b2 R a							 0  0 1 |   1   |   1   |   1    |    1
	 * 									 0  1 0 |   1   |   0   |   1    |    0
	 * a R b1 /\ a R b2 /\ b1 R b2		 0  1 1 |   1   |   1   |   1    |    1
	 * = a R b1 R b2					 1  0 0 |   0   |   1!  |   0    |    0!
	 * = a R b1							 1  0 1 |   1   |   1!  |   0    |    0!
	 * 									 1  1 0 |   0   |   0   |   1    |    0
	 * 									 1  1 1 |   1   |   1   |   1    |    1
	 * 
	 * (III)
	 * (A \/ B) /\ (C -> (D /\ (A -> E)))
	 * = (A /\ (C -> (D /\ E))) \/ (~A /\ (B /\ (C -> D)))	...distributive A
	 * = (A /\ (~C \/ (D /\ E))) \/ (~A /\ B /\ (~C \/ D))
	 * = (A /\ (~C \/ D) /\ (~C \/ E)) \/ (~A /\ B /\ ~C) \/ (~A /\ B /\ D)
	 * = (A \/ (~A /\ B /\ ~C) \/ (~A /\ B /\ D)) 
	 * 		/\ (~C \/ D \/ (~A /\ B /\ ~C) \/ (~A /\ B /\ D)) 
	 * 		/\ (~C \/ E \/ (~A /\ B /\ ~C) \/ (~A /\ B /\ D))
	 * = (A \/ (~A /\ B /\ ~C) \/ (~A /\ B /\ D)) 
	 * 		/\ (~C \/ D) /\ (~C \/ E \/ (~A /\ B /\ D))
	 * = (A \/ (~A /\ B /\ ~C) \/ (~A /\ B /\ D)) 
	 * 		/\ (~C \/ D) /\ (~C \/ E \/ ~A) /\ (~C \/ E \/ B) /\ (~C \/ E \/ D)
	 * = (A \/ ((~A /\ B) /\ (~C \/ D))) /\ (~C \/ D) /\ (~C \/ E \/ (~A /\ B))
	 * = ((~A /\ B) /\ (~C \/ D)) \/ 
	 * 		(~(~A /\ B) /\ (A /\ (~C \/ D) /\ (~C \/ E)))	...distributive ~A /\ B
	 * = ((~A /\ B) \/ ((A \/ ~B) /\ A /\ (~C \/ E))) /\ (~C \/ D)
	 * = ((~A /\ B) \/ (A /\ (~C \/ E))) /\ (~C \/ D)
	 * = ((~A /\ B) \/ (A /\ (C -> E))) /\ (C -> D)
	 * = ??(((~A /\ B) \/ A) /\ ((~A /\ B) \/ (~C \/ E))) /\ (~C \/ D)
	 * = ??
	 * = (A \/ B) /\ (~C \/ (D /\ (~A \/ E)))
	 * = (A \/ B) /\ (~C \/ (D /\ ~A) \/ (D /\ E))
	 * = ((A \/ B) /\ ~C) \/ ((A \/ B) /\ D /\ ~A) \/ ((A \/ B) /\ D /\ E)
	 * = ((A \/ B) /\ ~C) \/ (A /\ D /\ ~A) \/ (B /\ D /\ ~A) \/ ((A \/ B) /\ D /\ E)
	 * = ((A \/ B) /\ ~C) \/ (D /\ ((B /\ ~A) \/ ((A \/ B) /\ E)))
	 * 		...	A B | A\/B B/\~A = (A\/B)/\~A
	 * 			0 0 |	0	0
	 * 			0 1 |	1	1
	 * 			1 0 |	1	0
	 * 			1 1 |	1	0
	 * = ??((A \/ B) /\ ~C) \/ (D /\ (((A \/ B) /\ ~A) \/ ((A \/ B) /\ E)))
	 * 
	 * (Forall)
	 * (Forall x A(x) -> (B(x) /\ C(x)) /\ D) /\ B
	 * = Forall x A(x) -> (B(x) /\ C(x)) /\ D /\ (Exists x T -> B(x))
	 * = Forall x A(x) -> (B(x) /\ C(x)) /\ D
	 * 
	 * (A /\ B) /\ Forall x C(x)->A(x)			B C A C->A Fa Fa/\C formula 	C A C->A /\C  /\~C
	 * = (Forall x C(x)->A(x) /\ B) /\ A		0 0 0	1	1	0	0			0 0	1	 0		1
	 * = Forall x C(x)->A(x) /\ B /\ A			0 0 1 	1	1	0	0			0 1	1	 0		1
	 * 		...to make A/Fa a singleton			0 1 0	0	0	0	0			1 0	0	 0		0
	 * = (C /\ Fa(C->A) /\ B) \/ (~C /\ A /\ B)	0 1 1	1	?	Fa	0 			1 1	1	 1		0
	 * = (Fa(C->A) /\ B) /\ ??(~(C/\~A) /\ C)	1 0 0	1	1	0	0
	 * = (Fa(C->A) /\ B) /\ (~C\/A /\ C)		1 0 1 	1	1	0	1	
	 * = (Fa(C->A) /\ B) /\ (C->A /\ C)			1 1 0 	0	0	0	0	
	 * = ??Fa(C->A) /\ B /\ C					1 1 1 	1	?	Fa	Fa		
	 * 
	 * 											C B Fa(A)	Fa(C->A) formula
	 * 											0 0 0		1			0
	 * 											0 0 1		1			0
	 * 											0 1 0		1			A
	 * 											0 1 1		1			1
	 * 											1 0 0		0/1			0
	 * 											1 0 1		1			0
	 * 											1 1 0		0/1			Fa(C->A)
	 * 											1 1 1		1			1
	 * 
	 * 										Fa(C) B A	Fa(C->A)	formula
	 * 											0 0 0	0/1			0
	 * 											0 0 1	0/1			0
	 * 											0 1 0	0/1			0
	 * 											0 1 1	0/1			Fa(C->A)
	 * 											1 0 0	0			0
	 * 											1 0 1	0/1			0
	 * 											1 1 0	0			0
	 * 											1 1 1	0/1			Fa(C->A)
	 * 
	 * 										X:												Y:Fa(A\/
	 * 										Fa(C->A) B A formula	Fa(C)	Fa(A)	X/\B	(C->A)) 
	 * 											0	 0 0	0		1		0		0		?
	 * 											0	 0 1 	0		1		0		0
	 * 											0	 1 0	0		1		0		0
	 * 											0	 1 1	0		1		0		0
	 * 											1	 0 0	0		0		0		0
	 * 											1	 0 1 	0		0/1		0/1		0
	 * 											1	 1 0 	0		0		0		1
	 * 											1	 1 1 	1		0/1		0/1		1
	 * 
	 * 										Fa(C) Fa(A) B	A	Fa(C->A)	formula
	 * 											0	0	0 0/1	0/1			0
	 * 											0	0	1 0/1	0/1			Fa/\A
	 * 											0	1	0	1	1			0
	 * 											0	1	1	1	1			1
	 * 											1	0	0 0/1	0			0
	 * 											1	0	1 0/1	0			0
	 * 											1	1	0	1	1			0
	 * 											1	1	1	1	1			1
	 * 
	 * = ~C1\/A1 /\ ~C2\/A2 /\.../\ ~Cn\/An /\ B /\ (A1 \/ A2 \/...\/ An)
	 * = (~C1\/A1 /\ ~C2\/A2 /\.../\ ~Cn\/An /\ B /\ A1) \/ 
	 * 	 (~C1\/A1 /\ ~C2\/A2 /\.../\ ~Cn\/An /\ B /\ A2) \/...\/ 
	 * 	 (~C1\/A1 /\ ~C2\/A2 /\.../\ ~Cn\/An /\ B /\ An)
	 * 		...X\/Y /\ Z /\ Y = X\/Y /\ Z /\ Y\/F = Y\/(X/\F) /\ Z = Z /\ Y
	 * = (A1 /\ ~C2\/A2 /\.../\ ~Cn\/An /\ B) \/ 
	 * 	 (~C1\/A1 /\ A2 /\.../\ ~Cn\/An /\ B) \/...\/ 
	 * 	 (~C1\/A1 /\ ~C2\/A2 /\.../\ An /\ B)
	 * = f1 \/ f2 \/...\/ fn
	 * = ??
	 * 		...Fa(X) \/ Fa(Y) = X1/\X2/\.../\Xn \/ Y1/\Y2/\.../\Yn 
	 * 			= 	Fa(X)\/Y1 /\ Fa(X)\/Y2 /\.../\ Fa(X)\/Yn
	 * 			= 	X1\/Y1 /\ X2\/Y1 /\.../\ Xn\/Y1 /\ 
	 * 				X1\/Y2 /\ X2\/Y2 /\.../\ Xn\/Y2 /\.../\
	 * 				X1\/Yn /\ X2\/Yn /\.../\ Xn\/Yn
	 * 			=	??
	 * 
	 * 		...										X:													
	 * 			B C1 C2 ... Cn A1 A2 ... An-1 An Fx(C->A) formula X/\B/\C 
	 * 			0 0	 0	... 0	0  0 ...	0  0	1			0		0	
	 * 			0 0  0	...	0	0  0 ...	0  1	1			0		0
	 * 					...			 ...
	 * 			0 0  0	...	1	0  0 ...	0  0	0			0		0
	 * 			0 0  0	...	1	0  0 ... 	0  1	1			0		0
	 * 			0 0  0	...	1	0  0 ... 	1  0	0			0		0
	 * 					...			 ...
	 * 			1 0  0	...	0	0  0 ... 	0  1	1			1		0
	 * 			??
	 * 
	 * = ??~C1\/A1 /\ ~C2\/A2 /\.../\ ~Cn\/An /\ B /\ (~Fx(~C) ??\/ Fx(A))
	 * = ~C1\/A1 /\ ~C2\/A2 /\.../\ ~Cn\/An /\ B /\ ~(~C1 /\ ~C2 /\.../\ ~Cn)
	 * = ~C1\/A1 /\ ~C2\/A2 /\.../\ ~Cn\/An /\ B /\ (C1 \/ C2 \/...\/ Cn)
	 * = (~C1\/A1 /\ ~C2\/A2 /\.../\ ~Cn\/An /\ B /\ C1) \/ 
	 * 	 (~C1\/A1 /\ ~C2\/A2 /\.../\ ~Cn\/An /\ B /\ C2) \/...\/ 
	 * 	 (~C1\/A1 /\ ~C2\/A2 /\.../\ ~Cn\/An /\ B /\ Cn)
	 * 		...X\/Y /\ Z /\ ~Y = ((X /\ ~Y) \/ (Y /\ ~Y)) /\ Z = X /\ ~Y /\ Z
	 * = (C1/\A1 /\ ~C2\/A2 /\.../\ ~Cn\/An /\ B) \/ 
	 * 	 (~C1\/A1 /\ C2/\A2 /\.../\ ~Cn\/An /\ B) \/...\/ 
	 * 	 (~C1\/A1 /\ ~C2\/A2 /\.../\ Cn/\An /\ B)
	 * = (A1 /\ ~C2\/A2 /\.../\ ~Cn\/An /\ B /\ C1) \/
	 * 	 (~C1\/A1 /\ A2 /\.../\ ~Cn\/An /\ B /\ C2) \/...\/ 							
	 * 	 (~C1\/A1 /\ ~C2\/A2 /\.../\ An /\ B /\ Cn)
	 * 		...f1/\C1 \/ f2/\C2 \/...\/ fn/\Cn = f1 \/ f2 \/...\/ fn \/ ??C1/\C2/\.../\Cn
	 * = ??Forall x (C(x)->A(x)) /\ B												
	 * 
	 * (Forall x c1<=x<=c2->a(x)=a'(x) /\ B) /\ a(x)=a'(x)
	 * = a(c1)=a'(c1) /\.../\ a(c2)=a'(c2) /\ B /\ a(x)=a'(x)
	 * = a(c1)=a'(c1) /\.../\ a(c2)=a'(c2) /\ B
	 * 
	 * Merging transitive operands if they share a common one at ends.
	 * Explicitly for total ordering {@link Imply} and {@link OrderRelation}. 
	 * 
	 * Handled separately for non-ordering {@link Equality#andReduced(Proposition)} 
	 * and non-common-ordering {@link And#andReduced(Proposition)} 
	 * and {@link Or#orByReduce(Proposition)}.
	 * 
	 * Except for in-equalities since A != B /\ B != C not necessarily implies
	 * A != C.
	 * 
	 * @param p2
	 * @return
	 */
	protected Proposition andByReduce(Proposition p2) {
		return null;
	}
	
	/**
	 * @param p2
	 * @return
	 */
	private Proposition andByReduce(And p2) {
		boolean isReduced = false;
		List<Proposition> B = new ArrayList<>();
		B: for (Proposition b : p2.getPropositions()) {
			// A /\ (B /\ T) = A /\ B
			if (b.isTrue()) continue;
			
			// A /\ (B /\ A) = B /\ A
			if (equals(b)) return p2;
			
			// optimization by merging with contradiction
			// A /\ (B /\ ~A) = F, A /\ (B /\ F) = F
			if (equals(b.not()) || b.isFalse()) return 
					False.from("A && (B && ~A) = F, A && (B && F) = F", Operator.And, this, p2);
			
			if (!isReduced) {
				Relation.Operator bOp = b.getOp();
				List<Proposition> D = new ArrayList<>();
				if (bOp == Predicate.Operator.Forall) {
					/*
					 * A /\ (B /\ Fx(C /\ A))
					 * = A /\ B /\ Fx(C) /\ Fx(A)
					 * = Ex(A) /\ B /\ Fx(C) /\ Fx(A)	...given A depends on ONLY x
					 * = B /\ Fx(C) /\ Fx(A) 			...Fx(A) /\ Ex(A) = Fx(A)
					 * = p2
					 * 
					 * A && (B && Fx(C && A)) = (B && Fx(C && A)) && A = this	...given A depends on ONLY x
					 */
					Proposition result = p2.andByReduceForall(this, (Forall) b);
					if (result != null) return result;
					
				} else if (bOp == Operator.Or) {
					List<Proposition> C = new ArrayList<>();
					for (Proposition c : b.getPropositions()) {
						/*
						 * A /\ (B /\ (C \/ A))
						 * = A /\ B /\ (C \/ A)
						 * = (A /\ B /\ C) \/ (A /\ B /\ A)
						 * = (A /\ B /\ C) \/ (A /\ B)
						 * = (A /\ B /\ C) \/ (A /\ B /\ T)
						 * = A /\ B /\ (C \/ T)
						 * = A /\ B
						 */
						if (equals(c)) {isReduced = true; continue B;}
						/*
						 * A /\ (B /\ (C \/ (D /\ A)))
						 * = A /\ B /\ (C \/ (D /\ A))
						 * = A /\ B /\ (C \/ D) /\ (C \/ A)
						 * = A /\ B /\ (C \/ D)
						 * = A /\ (B /\ (C \/ D))
						 */
						if (c.getOp() == Operator.And) {
							for (Proposition d : c.getPropositions()) {
								if (equals(d)) isReduced = true;
								else D.add(d);
							}
							if (isReduced) c = And.from(D);
						}
						C.add(c);
					}
					if (isReduced) b = Or.from(C);
				
				} else if (bOp == Operator.Imply) {
					Imply bi = (Imply) b;
					Proposition bic = bi.consequent;
					
					/*
					 * A /\ (B /\ (C -> A))
					 * = A /\ B /\ (~C \/ A)
					 * = (A /\ B /\ ~C) \/ (A /\ B /\ A)
					 * = (A /\ B /\ ~C) \/ (A /\ B /\ T)
					 * = A /\ B /\ (~C \/ T)
					 * = A /\ B
					 */
					if (equals(bic)) {isReduced = true; continue;}
					
					Proposition bia = bi.antecedent;
					/*
					 * A /\ (B /\ (A -> C))
					 * = A /\ (~A \/ C) /\ B
					 * = (A /\ ~A) \/ (A /\ C)) /\ B
					 * = A /\ C /\ B
					 */
					if (equals(bia)) {b = bic; isReduced = true;}
					
					Relation.Operator biaOp = bia.getOp();
					/*
					 * A /\ (B /\ ((D /\ A) -> C))
					 * = A /\ B /\ (~(D /\ A) \/ C)
					 * = A /\ B /\ (~D \/ ~A \/ C)
					 * = (A /\ B /\ ~D) \/ (A /\ B /\ ~A) \/ (A /\ B /\ C)
					 * = (A /\ B /\ ~D) \/ (A /\ B /\ C)
					 * = A /\ B /\ (~D \/ C)
					 * = A /\ (B /\ (D -> C))
					 */
					final Supplier<Proposition> bicSp = ()-> bic;
					if (biaOp == Operator.And) {
						for (Proposition d : bia.getPropositions()) {
							if (equals(d)) isReduced = true;
							else D.add(d);
						}
						if (isReduced) b = And.from(D).imply(bicSp);
					}
					else if (biaOp == Operator.Or) {
						boolean isReduced2 = false;
						for (Proposition d : bia.getPropositions()) {
							/*
							 * A /\ (B /\ ((A \/ D) -> C))
							 * = A /\ B /\ (~(A \/ D) \/ C)
							 * = A /\ B /\ ((~A /\ ~D) \/ C)
							 * = A /\ B /\ (~A \/ C) /\ (~D \/ C)
							 * = B /\ ((A /\ ~A) \/ (A /\ C)) /\ (~D \/ C)
							 * = B /\ A /\ C /\ (~D \/ C)
							 * = B /\ A /\ C
							 * = A /\ (B /\ C)
							 */
							if (equals(d)) {isReduced2 = true; b = bic; break;}
							
							/*
							 * A /\ (B /\ ((D \/ (E /\ A)) -> C))
							 * = A /\ B /\ (~(D \/ (E /\ A)) \/ C)
							 * = A /\ B /\ ((~D /\ ~(E /\ A)) \/ C)
							 * = A /\ B /\ ((~D /\ (~E \/ ~A)) \/ C)
							 * = A /\ B /\ (~D \/ C) /\ (~E \/ ~A \/ C))
							 * = (~D \/ C) /\ ((A /\ B /\ ~E) \/ (A /\ B /\ ~A) \/ (A /\ B /\ C))
							 * = (~D \/ C) /\ ((A /\ B /\ ~E) \/ (A /\ B /\ C))
							 * = A /\ B /\ (~D \/ C) /\ (~E \/ C)
							 * = A /\ B /\ ((~D /\ ~E) \/ C)
							 * = A /\ B /\ (~(D \/ E) \/ C)
							 * = A /\ (B /\ ((D \/ E) -> C))
							 */
							else if (d.getOp() == Operator.And) {
								List<Proposition> E = new ArrayList<>();
								for (Proposition e : d.getPropositions()) {
									if (equals(e)) isReduced = true;
									else E.add(e);
								}
								if (isReduced) d = And.from(E);
							}
							D.add(d);
						}
						if (isReduced) b = Or.from(D).imply(bicSp);
						if (isReduced2) isReduced = true;
					}
				}
			}
			B.add(b);
		}
		
		return isReduced ? and(B) : null;
	}
	
	/**
	 * A /\ (A \/ B)
	 * = A
	 * 
	 * A /\ (~A \/ B)
	 * = (A /\ ~A) \/ (A /\ B)
	 * = A /\ B
	 * 
	 * A /\ (B \/ ~(C /\ (A -> D)))
	 * = A /\ (B \/ ~(C /\ (~A \/ D)))
	 * = A /\ (B \/ ~C \/ ~(~A \/ D))
	 * = A /\ (B \/ ~C \/ (A /\ ~D))
	 * = A /\ (B \/ ~C \/ A) /\ (B \/ ~C \/ ~D)
	 * = A /\ (B \/ ~C \/ ~D)
	 * = A /\ (B \/ ~(C /\ D))
	 * 
	 * A /\ (B \/ (C /\ A))
	 * = (A /\ B) \/ (A /\ C /\ A)
	 * = (A /\ B) \/ (A /\ C)
	 * = A /\ (B \/ C)
	 * 
	 * A /\ (B \/ (C /\ (D \/ A)))
	 * = (A /\ B) \/ (A /\ C /\ (D \/ A))
	 * = (A /\ B) \/ (A /\ C)
	 * = A /\ (B \/ C)
	 * 
	 * A /\ (B \/ (C /\ (D \/ (E /\ A))))
	 * = (A /\ B) \/ (A /\ C /\ (D \/ (E /\ A)))
	 * = (A /\ B) \/ (A /\ C /\ D) \/ (A /\ C /\ E /\ A)
	 * = (A /\ B) \/ (A /\ C /\ D) \/ (A /\ C /\ E)
	 * = (A /\ B) \/ (A /\ C /\ (D \/ E))
	 * = A /\ (B \/ (C /\ (D \/ E)))
	 * 
	 * A /\ (B \/ (C /\ (D \/ (E /\ (F \/ (G /\ A))))))
	 * = (A /\ B) \/ (A /\ C /\ (D \/ (E /\ (F \/ (G /\ A)))))
	 * = (A /\ B) \/ (A /\ C /\ D) \/ (A /\ C /\ E /\ (F \/ (G /\ A)))
	 * = (A /\ B) \/ (A /\ C /\ D) \/ (A /\ C /\ E /\ F) \/ (A /\ C /\ E /\ G /\ A)
	 * = (A /\ B) \/ (A /\ C /\ D) \/ (A /\ C /\ E /\ F) \/ (A /\ C /\ E /\ G)
	 * = A /\ (B \/ (C /\ (D \/ (E /\ (F \/ G)))))
	 *
	 * @param p2
	 * @return
	 */
	private Proposition andByReduce(Or p2) {
		assert p2 != null;
		
		boolean isReduced = false;
		List<Proposition> B = new ArrayList<>();
		for (Proposition b : p2.getPropositions()) {
			// A /\ (A \/ B) = A
			if (equals(b)) return this;
			
			if (!isReduced) {
				// A /\ (~A \/ B) = A /\ B
				if (equals(b.not())) {isReduced = true; continue;}
				
				Relation.Operator bOp = b.getOp();
				if (bOp instanceof Operator) {
					List<Proposition> C = new ArrayList<>();
					switch ((Operator) bOp) {
					case And:
						C: for (Proposition c : ((And) b).getPropositions()) {
							if (!isReduced) {
								// A /\ (B \/ (C /\ A)) = A /\ (B \/ C)
								if (equals(c)) {isReduced = true; continue;}
								
								if (c.getOp() == Operator.Or) {
									List<Proposition> D = new ArrayList<>();
									for (Proposition d : ((Or) c).getPropositions()) {
										// A /\ (B \/ (C /\ (D \/ A))) = A /\ (B \/ C)
										if (equals(d)) {isReduced = true; continue C;}
										
										if (d.getOp() == Operator.And) {
											List<Proposition> E = new ArrayList<>();
											for (Proposition e : ((And) d).getPropositions()) {
												if (!isReduced) {
													// A /\ (B \/ (C /\ (D \/ (E /\ A)))) 
													//	= A /\ (B \/ (C /\ (D \/ E)))
													if (equals(e)) {isReduced = true; continue;}
													
													// A /\ (B \/ (C /\ (D \/ (E /\ (F \/ (G /\ A))))))
													//	= A /\ (B \/ (C /\ (D \/ (E /\ (F \/ G)))))
													if (e.getOp() == Operator.Or) {
														List<Proposition> F = new ArrayList<>();
														for (Proposition f : ((Or) e).getPropositions()) {
															if (f.getOp() == Operator.And) {
																List<Proposition> G = new ArrayList<>();
																for (Proposition g : ((And) f).getPropositions()) {
																	if (equals(g)) isReduced = true;
																	else G.add(g);
																}
																if (isReduced) f = And.from(G);
															}
															F.add(f);
														}
														if (isReduced) e = Or.from(F);
													}
												}
												E.add(e);
											}
											if (isReduced) d = And.from(E);
										}
										D.add(d);
									}
									if (isReduced) c = Or.from(D);
								}
							}
							C.add(c);
						}
						if (isReduced) b = And.from(C);
						break;
						
					case Not:
						// A /\ (B \/ ~(C /\ (A -> D))) = A /\ (B \/ ~(C /\ D))
						Proposition bn = b.not();
						if (bn.getOp() == Operator.And) {
							for (Proposition c : ((And) bn).getPropositions()) {
								if (c.getOp() == Operator.Imply) {
									Imply ci = (Imply) c;
									if (equals(ci.antecedent)) {
										c = ci.consequent; isReduced = true;}
								}
								C.add(c);
							}
							if (isReduced) b = And.from(C).not();
						}
						break;
						
					default:
					}
				}
			}
			B.add(b);
		}
		return isReduced ? and(()-> Or.from(B)) : null;
	}
	
	/**
	 * TODO: BooleanOptimizer.Rule
	 * 
	 * A /\ (A -> B)				A /\ (B -> A)
	 * = A /\ (~A \/ B)				= A /\ (~B \/ A)
	 * = (A /\ ~A) \/ (A /\ B)		= A
	 * = (A /\ B)					
	 * 
	 * A /\ ((A /\ B) -> C)
	 * = A /\ (~(A /\ B) \/ C)
	 * = A /\ (~A \/ ~B \/ C)
	 * = (A /\ ~A) \/ (A /\ ~B) \/ (A /\ C)
	 * = (A /\ ~B) \/ (A /\ C)
	 * = A /\ (~B \/ C)
	 * = A /\ (B -> C)
	 * 
	 * A /\ (B -> (A /\ C)) 		= A /\ (B -> (C /\ A))
	 * = A /\ (~B \/ (C /\ A))
	 * = A /\ (~B \/ C) /\ (~B \/ A)
	 * = A /\ (~B \/ C)
	 * = A /\ (B -> C)
	 * 
	 * A /\ (B -> (C /\ (D -> A)))
	 * = A /\ (B -> (C /\ (~D \/ A)))
	 * = A /\ (B -> ((C /\ ~D) \/ (C /\ A)))
	 * = A /\ (~B \/ (C /\ ~D) \/ (C /\ A))
	 * = (A /\ ~B) \/ (A /\ C /\ ~D) \/ (A /\ C)
	 * = A /\ (~B \/ (C /\ ~D) \/ C)
	 * = A /\ (~B \/ C)
	 * = A /\ (B -> C)
	 * 
	 * A /\ (B -> (C /\ (D \/ A)))
	 * = A /\ (~B \/ (C /\ (D \/ A)))
	 * = (A /\ ~B) \/ (A /\ C /\ (D \/ A))
	 * = (A /\ ~B) \/ (A /\ C)
	 * = A /\ (B -> C)
	 * 
	 * A /\ (B -> (C /\ (D -> (E /\ (F -> A)))))
	 * = A /\ (~B \/ (C /\ (~D \/ (E /\ (~F \/ A)))))
	 * = (A /\ ~B) \/ (A /\ C /\ (~D \/ (E /\ (~F \/ A))))
	 * = (A /\ ~B) \/ (A /\ C /\ ~D) \/ (A /\ C /\ E /\ (~F \/ A))
	 * = (A /\ ~B) \/ (A /\ C /\ ~D) \/ (A /\ C /\ E)
	 * = A /\ (~B \/ (C /\ (~D \/ E)))
	 * = A /\ (B -> (C /\ (D -> E)))
	 * 
	 * A /\ (B -> Forall(C /\ A))
	 * = (A0\/A1\/...\/An) /\ (~B \/ [Forall(C) /\ A0/\A1/\.../\An])
	 * = (A0\/A1\/...\/An) /\ [~B \/ Forall(C)] /\ [~B \/ (A0/\A1/\.../\An)]
	 * = [~B \/ Forall(C)] /\ 
	 * 		([(A0\/A1\/...\/An) /\ ~B] \/ [(A0\/A1\/...\/An) /\ (A0/\A1/\.../\An)])
	 * = [~B \/ Forall(C)] /\ ([(A0\/A1\/...\/An) /\ ~B] \/ [A0/\A1/\.../\An])	... (X\/Y) /\ X/\Y = X/\Y
	 * = [~B \/ Forall(C)] /\ (A0\/A1\/...\/An \/ [A0/\A1/\.../\An]) /\ (~B \/ [A0/\A1/\.../\An])
	 * = [~B \/ Forall(C)] /\ (A0\/A1\/...\/An) /\ (~B \/ [A0/\A1/\.../\An])	... X\/Y \/ (X/\Y) = X\/Y
	 * = [~B \/ Forall(C)] /\ A /\ (~B \/ Forall(A))
	 * = ignoresDependency
	 * 
	 * A /\ (B -> (C /\ Forall(D /\ (E -> A))))
	 * = A /\ (~B \/ (C /\ Forall(D /\ (~E \/ A))))
	 * = A /\ (~B \/ (C /\ ForallD /\ Forall(~E \/ A)))
	 * = (A0\/A1\/...\/An) /\ (~B \/ [C /\ ForallD /\(~E0\/A0)/\(~E1\/A1)/\.../\(~En\/An)])
	 * = (A0\/A1\/...\/An) /\ (~B \/ C) /\ (~B \/ ForallD) /\ (~B\/~E0\/A0) /\ (~B\/~E1\/A1) /\.../\ (~B\/~En\/An)
	 * = ignoresDependency
	 * 
	 * A /\ (((A /\ D) \/ C) -> B)
	 * = A /\ (~((A /\ D) \/ C) \/ B)
	 * = A /\ ((~(A /\ D) /\ ~C) \/ B)
	 * = A /\ (((~A \/ ~D) /\ ~C) \/ B)
	 * = A /\ ((~A /\ ~C) \/ (~D /\ ~C) \/ B)
	 * = (A /\ ~A /\ ~C) \/ (A /\ ~D /\ ~C) \/ (A /\ B)
	 * = (A /\ ~D /\ ~C) \/ (A /\ B)
	 * = A /\ ((~D /\ ~C) \/ B)
	 * = A /\ (~(D \/ C) \/ B)
	 * = A /\ ((D \/ C) -> B)
	 * 
	 * A /\ ((A \/ B) -> C)
	 * = A /\ (~(A \/ B) \/ C)
	 * = A /\ ((~A /\ ~B) \/ C)
	 * = A /\ (~A \/ C) /\ (~B \/ C)
	 * = ((A /\ ~A) \/ (A /\ C)) /\ (~B \/ C)
	 * = A /\ C /\ (~B \/ C)
	 * = A /\ C /\ (B -> C)
	 * 
	 * A /\ ((B /\ (C -> A)) -> D)
	 * = A /\ (~(B /\ (~C \/ A)) \/ D)
	 * = A /\ (~B \/ (C /\ ~A) \/ D)
	 * = (A /\ ~B) \/ (A /\ C /\ ~A) \/ (A /\ D)
	 * = (A /\ ~B) \/ (A /\ D)
	 * = A /\ (B -> D)
	 * 
	 * A /\ ((B /\ (C -> (D /\ A))) -> E)
	 * = A /\ (~(B /\ (~C \/ (D /\ A))) \/ E)
	 * = A /\ ((~B \/ ~(~C \/ (D /\ A))) \/ E)
	 * = A /\ ((~B \/ (C /\ (~D \/ ~A))) \/ E)
	 * = (A /\ (~B \/ (C /\ (~D \/ ~A)))) \/ (A /\ E)
	 * = (A /\ ~B) \/ (A /\ C /\ (~D \/ ~A)) \/ (A /\ E)
	 * = (A /\ ~B) \/ (A /\ C /\ ~D) \/ (A /\ C /\ ~A) \/ (A /\ E)
	 * = (A /\ ~B) \/ (A /\ C /\ ~D) \/ (A /\ E)
	 * = A /\ (~B \/ (C /\ ~D) \/ E)
	 * = A /\ (~B \/ ~(~C \/ D) \/ E)
	 * = A /\ (~(B /\ (~C \/ D)) \/ E)
	 * = A /\ ((B /\ (C -> D)) -> E)
	 * 
	 * A /\ ((B /\ ~(C /\ A)) -> D)
	 * = A /\ (~(B /\ ~(C /\ A)) \/ D)
	 * = A /\ (~B \/ (C /\ A) \/ D)
	 * = (A /\ ~B) \/ (C /\ A) \/ (A /\ D)
	 * = A /\ (~B \/ C \/ D)
	 * = A /\ (B -> (C \/ D))
	 * 
	 * @param p2
	 * @return
	 */
	private Proposition andByReduce(Imply p2) {
		assert p2 != null;
		Proposition p2a = p2.antecedent, p2c = p2.consequent;
		Supplier<Proposition> p2cSp = ()-> p2c;
		
		// A 						/\ (A -> B) 				= (A /\ B)
		if (equals(p2a)) return p2a.and(p2cSp); // avoiding mutable Iff.and(...)

		// A 						/\ (B -> A)					= A
		if (equals(p2c)) return this;
		
		boolean isReduced = false, isReduced2 = false; 
		List<Proposition> C = new ArrayList<>();
		
		Relation.Operator p2aOp = p2a.getOp();
		if (p2aOp == Operator.Or) {
			for (Proposition c : p2a.getPropositions()) {
				if (!isReduced && !isReduced2) {
					// A /\ ((A \/ C) -> B) = A /\ B /\ (C -> B)
					if (equals(c)) {isReduced = true; continue;}
					
					// A /\ (((A /\ D) \/ C) -> B) = A /\ ((D \/ C) -> B)
					if (c.getOp() == Operator.And) {
						List<Proposition> D = new ArrayList<>();
						for (Proposition d : c.getPropositions()) {
							if (equals(d)) isReduced2 = true; 
							else D.add(d);
						}
						if (isReduced2) c = And.from(D);
					}
				}
				C.add(c);
			}
			if (isReduced || isReduced2) {
				Proposition cib = and(()-> Or.from(C).imply(p2cSp));
				return isReduced ? and(p2cSp).and(()-> cib) : cib;
			}

		}
		else if (p2aOp == Operator.And) {
			List<Proposition> B = new ArrayList<>();
			for (Proposition b : p2a.getPropositions()) {
				if (!isReduced && !isReduced2) {
					// A /\ ((A /\ B) -> C) = A /\ (B -> C)
					if (equals(b)) {isReduced = true; continue;}
					
					/*
					 * A /\ (((A \/ C) /\ B) -> D)
					 * = A /\ (~((A \/ C) /\ B) \/ D)
					 * = A /\ ((~(A \/ C) \/ ~B) \/ D)
					 * = A /\ (((~A /\ ~C) \/ ~B) \/ D)
					 * = A /\ ((~A /\ ~C) \/ ~B \/ D)
					 * = A /\ (~A \/ ~B \/ D) /\ (~C \/ ~B \/ D)
					 * = ((A /\ ~A) \/ (A /\ ~B) \/ (A /\ D)) /\ (~C \/ ~B \/ D)
					 * = ((A /\ ~B) \/ (A /\ D)) /\ (~C \/ ~B \/ D)
					 * = A /\ (~B \/ D) /\ (~C \/ ~B \/ D)
					 * = A /\ (~B \/ D)		...X /\ (Y\/X) = X
					 * = A /\ (B -> D)
					 */
					ReductionOperations ros = new ReductionOperations();
					ros.add("A && (((A || C) && B) -> D) = A && (B -> D)",
							Operator.Or, (b_, c)-> equals(c), null, null, null);
					b.reduceByOperands(ros, false);
					if (ros.isReduced(0)) {isReduced = true; continue;}

					Relation.Operator bOp = b.getOp();
					if (bOp instanceof Operator) switch ((Operator) bOp) {
					case Imply:
						Imply bi = (Imply) b; Proposition bic = bi.consequent;
						// A 	/\ ((B /\ (C -> A)) 		-> D) = A /\ (B -> D)
						if (equals(bic)) {isReduced = true; continue;}
						
						// A 	/\ ((B /\ (D -> (C /\ A))) 	-> E) = A /\ ((B /\ (D -> C)) -> E)
						if (bic.getOp() == Operator.And) {
							for (Proposition c : ((And) bic).getPropositions()) {
								if (equals(c)) isReduced = true;
								else C.add(c);
							}
							if (isReduced) b = bi.antecedent.imply(()-> And.from(C));
						}
						break;
						
					case Not:
						// A 	/\ ((B /\ ~(C /\ A)) 		-> D) = A /\ (B -> (C \/ D))
						Proposition bn = b.not();
						if (bn.getOp() == Operator.And) 
							for (Proposition c : ((And) bn).getPropositions()) {
								if (equals(c)) isReduced2 = true;
								else C.add(c);
							}
						if (isReduced2) continue;
						break;
					default:
					}
				}
				B.add(b);
			}
			if (isReduced || isReduced2) {
				final boolean isReduced_ = isReduced;
				return and(()-> And.from(B).imply(
						isReduced_ ? p2cSp : ()-> And.from(C).or(p2cSp)));
			}
		}
		
		Relation.Operator p2cOp = p2c.getOp();
		if (p2cOp == Operator.And) {
			isReduced = false;
			C.clear();
			C: for (Proposition c : ((And) p2c).getPropositions()) {
				if (!isReduced) {
					// A 	 /\ (B -> (C /\ A)) 					 = A /\ (B -> C)
					if (equals(c)) {isReduced = true; continue;} 
					
					Relation.Operator cOp = c.getOp();
					if (cOp instanceof Operator) switch ((Operator) cOp) {
					case Or:
						// A /\ (B -> (C /\ (D \/ A))) = A /\ (B -> C)
						for (Proposition d : ((Or) c).getPropositions()) 
							if (equals(d)) {isReduced = true; continue C;}
						break;

					case Imply:
						Imply ci = (Imply) c;
						Proposition cic = ci.consequent;
						// A /\ (B -> (C /\ (D -> A)))				 = A /\ (B -> C)
						if (equals(cic)) {isReduced = true; continue;}
						
						// A /\ (B -> (C /\ (D -> (E /\ (F -> A))))) = A /\ (B -> (C /\ (D -> E)))
						if (cic.getOp() == Operator.And) {
							List<Proposition> E = new ArrayList<>();
							for (Proposition e : ((And) cic).getPropositions()) {
								if (e.getOp() == Operator.Imply) {
									Proposition eic = ((Imply) e).consequent;
									if (equals(eic)) {isReduced = true; continue;}
								}
								E.add(e);
							}
							if (isReduced) c = ci.antecedent.imply(()-> And.from(E));
						}
						break;
						
					default:
						break;

					} else if (cOp == Predicate.Operator.Forall) 
						// A /\ (B -> (C /\ Forall(D /\ (E -> A)))) = ignoresDependency
						ignoreDependency(Operator.And, p2);
				}
				C.add(c);	// not else, for the inner else above
			}
			if (isReduced) return and(()-> p2a.imply(()-> And.from(C)));
			
		} else if (p2cOp == Predicate.Operator.Forall) 
			// A /\ (B -> Forall(C /\ A)) = ignoresDependency
			ignoreDependency(Operator.And, p2);
		
		return null;
	}
	
	/**
	 * DeMorgan's Law:
	 * A /\ ~\/Bn
	 * = A /\ /\~Bn
	 * 
	 * @param p2
	 * @return
	 */
	private Proposition andByReduce(Not p2) {
		assert p2 != null;
		
		Proposition result = this, p2n = p2.not();
		if (p2n.getOp() == Operator.Or) 
			for (Proposition Bn : p2n.getPropositions())
				result = result.and(()-> Bn.not());
		return result;
	}
	
	/**
	 * A /\ T = A
	 * 
	 * @param p2
	 * @return
	 */
	private Proposition andByReduce(True p2) {
		return this;
	}
	
	/**
	 * A /\ F = F
	 * 
	 * @param p2
	 * @return
	 */
	private Proposition andByReduce(False p2) {
		assert p2 != null;
		return False.from(Operator.And, p2);
	}
	
	private Proposition andByReduce(Predicate p2) {
		try {
			if (p2.getOp().equals(Predicate.Operator.Forall)) return andByReduce((Forall) p2);
		} catch (ClassCastException e) {
			returnTodoException("unsupported forall?");
		}
		return null;
	}

	private Proposition andByReduce(Forall p2) {
		assert p2 != null;
		final Proposition fap = p2.getProposition();
		final ReductionOperations ros = new ReductionOperations();
		
		/*
		 * A && Fx(A)
		 * = Ey(A) && Fx(A)		...given A dependent on more than x
		 * = (Axy1 || Axy2 ||...|| Axym) && (Ax1 && Ax2 &&...&& Axn)
		 * 
		 * A && Fx(A)
		 * = Ex(A) && Fx(A)		...given A dependent on ONLY x
		 * = (Ax1 || Ax2 ||...|| Axn) && (Ax1 && Ax2 &&...&& Axn)
		 * = (Ax1 && Ax2 &&...&& Axn) || (Ax1 && Ax2 &&...&& Axn) ||...|| (Ax1 && Ax2 &&...&& Axn)
		 * = Ax1 && Ax2 &&...&& Axn
		 * = Fx(A)
		 */
		ros.add("A && Fx(A) = Fx(A)				...given A dependent on ONLY x as Fx\n" +
				"A && Fx(A) = ignoresDependency	...given A dependent on more than x",
				null, 
				(X, a)-> equals(X), 
				null, null, 
				(X, newA) -> dependsOnTheSame(p2) ? p2 : ignoreDependency(Operator.And, p2));
		Proposition result = fap.reduceByOperands(ros, false);
		if (result != null) return result;
		
		/*
		 * A /\ Fx(B /\ Fy(C /\ Fz(D /\ Fw(E /\ A))))
		 * = A /\ Fx(B /\ Fy(C /\ Fz(D /\ Fw(E) /\ Fw(A))))
		 * = A /\ Fx(B /\ Fy(C /\ Fz(D) /\ Fzw(E) /\ Fzw(A)))
		 * = A /\ Fx(B /\ Fy(C) /\ Fyz(D) /\ Fyzw(E) /\ Fyzw(A))
		 * = Exyzw(A) /\ Fx(B) /\ Fxy(C) /\ Fxyz(D) /\ Fxyzw(E) /\ Fxyzw(A)	...given A depends on ONLY x, y, z and w
		 * = Fx(B) /\ Fxy(C) /\ Fxyz(D) /\ Fxyzw(E) /\ Fxyzw(A)				...Ex(A) /\ Fx(A) = Fx(A)
		 * = p2
		 */
		result = andByReduceForallAnd(p2, Arrays.asList(p2));
		if (result != null) return result;

		ros.clear();
		/*
		 * A && Fx(B -> A)
		 * = Ex(A) && Fx(B -> A)											...given A dependent on x as Fx
		 * = (A1 || A2 ||...|| An) && (~B1 || A1) && (~B2 || A2) &&...&& (~Bn || An)
		 * = (A1 && (~B1 || A1) && (~B2 || A2) &&...&& (~Bn || An)) 
		 * 		|| (A2 && (~B1 || A1) && (~B2 || A2) &&...&& (~Bn || An)) 
		 * 		||...|| (An && (~B1 || A1) && (~B2 || A2) &&...&& (~Bn || An))
		 * = (A1 && (~B2 || A2) &&...&& (~Bn || An)) 
		 * 		|| ((~B1 || A1) && A2 &&...&& (~Bn || An)) 
		 * 		||...|| ((~B1 || A1) && (~B2 || A2) &&...&& An)	...X && (~Y || X) = X
		 * = ((~T || A1) && (~B2 || A2) &&...&& (~Bn || An)) 
		 * 		|| ((~B1 || A1) && (~T || A2) &&...&& (~Bn || An)) 
		 * 		||...|| ((~B1 || A1) && (~B2 || A2) &&...&& (~T || An))
		 * = (Fx(B -> A) && B1=T) || (Fx(B -> A) && B2=T) ||...|| (Fx(B -> A) && Bn=T)
		 * = Fx(B -> A) && (B1=T || B2=T ||...|| Bn=T)
		 * = Fx(B -> A) && B
		 *
		 * A /\ Fx(A -> B)
		 * = Exists[y]A(y) /\ ~Exists[x]~(A(x) -> B(x))
		 * = Ex[y]A(y) /\ ~Ex[x]~(~A(x) \/ B(x))
		 * = Ex[y]A(y) /\ ~Ex[x](A(x) /\ ~B(x))
		 * = ??Ex[y]A(y) /\ ~Ex[x](A(x) /\ ~B(x))
		 * 
		 * = (A0 \/ A1 \/ ... \/ An) /\ (A0->B0) /\ (A1->B1) /\ ... /\ (An->Bn)
		 * = (A0 \/ A1 \/ ... \/ An) /\ (~A0\/B0) /\ (~A1\/B1) /\ ... /\ (~An\/Bn)
		 * = 	(A0 /\ (~A0\/B0) /\ (~A1\/B1) /\ ... /\ (~An\/Bn)) \/
		 * 		(A1 /\ (~A0\/B0) /\ (~A1\/B1) /\ ... /\ (~An\/Bn)) \/ ... \/
		 * 		(An /\ (~A0\/B0) /\ (~A1\/B1) /\ ... /\ (~An\/Bn))
		 * = 	(A0 /\ B0 		/\ (~A1\/B1) /\ ... /\ (~An\/Bn)) \/		...	X	Y |	~X\/Y	X/\(~X\/Y)
		 * 		(A1 /\ (~A0\/B0) /\ B1		 /\ ... /\ (~An\/Bn)) \/ ... \/		0	0 |	1		0
		 * 		(An /\ (~A0\/B0) /\ (~A1\/B1) /\ ... /\ Bn)						0	1 |	1		0
		 * 																		1	0 |	0		0
		 * A /\ (A -> B)				: A0/\(A0->~B0)/\(A0->B1) = T			1	1 |	1		1
		 * A /\ Exists[x](A(x) -> B(x))	: A0/\(A0->~B0)/\(A0->B1) = F
		 * A /\ Forall[x](A(x) -> B(x))	: A0/\(A0->~B0)/\(A0->B1) = F
		 * 
		 * A /\ Exists[x](A(x) -> B(x))	: A0/\A1/\(A0->B0)/\(A1->~B1) = T
		 * A /\ Forall[x](A(x) -> B(x))	: A0/\A1/\(A0->B0)/\(A1->~B1) = F
		 */
		final List<Forall> fs = new ArrayList<>(Arrays.asList(p2));
		final ReductionOctet fapImply = new ReductionOctet(
				"A && Fx(B -> A) = A && Fx(A -> B) = ignoresDependency	...given A dependent on x as Fx",
				Operator.Imply, 
				(X, ba)-> {Imply xi = (Imply) X; return equals(xi.antecedent) || equals(xi.consequent);}, 
				null, (X, ba)-> ((Imply) X).consequent, 
				(X, newBA) -> dependsOnTheSame(fs) ? ignoreDependency(Operator.And, p2) : null),
		/*
		 * A && Fx(B -> Fy(C -> A)) = Fx(B -> Fy(C -> A)) && A = ??Fx(B -> Fy(A -> C)) && A = ignoresDependency
		 * = Fx(~B || Fy(~C || A)) && Exy(A)	...given A depends on ONLY x and y 
		 * = Fx(~B || ((~Cy1 || Ay1) && (~Cy2 || Ay2) &&...&& (~Cyn || Ayn))) && (Ax1y1 || Ax2y2 ||...|| Axnym)
		 * = ignoresDependency 
		 */
		fa = new ReductionOctet(
				"A && Fx(B -> Fy(C -> A)) = ignoresDependency",
				Predicate.Operator.Forall, (Fy, Y)-> !fs.add((Forall) Fy), null, null, null);
		ros.add(fapImply);
		ros.add(fa);
		ros.add(fapImply);
		result = fap.reduceByOperands(ros, false);
		if (result != null) return result;
		
		fs.clear(); fs.add(p2);
		ros.clear();
		/*
		 * A && Fx(B -> (A && C))
		 * = Ex(A) && Fx(~B || (A && C))	...given A depends on ONLY x as Fx
		 * = (A1 || A2 ||...|| An) && (~B1 || (A1 && C1)) && (~B2 || (A2 && C2)) &&...&& (~Bn || (An && Cn))
		 * = (A1 && (~B1 || (A1 && C1)) && (~B2 || (A2 && C2)) &&...&& (~Bn || (An && Cn))) || 
		 * 		(A2 && (~B1 || (A1 && C1)) && (~B2 || (A2 && C2)) &&...&& (~Bn || (An && Cn))) ||...|| 
		 * 		(An && (~B1 || (A1 && C1)) && (~B2 || (A2 && C2)) &&...&& (~Bn || (An && Cn)))
		 * = (A1 && (~B1 || A1) && (~B1 || C1) && (~B2 || (A2 && C2)) &&...&& (~Bn || (An && Cn))) || 
		 * 		(A2 && (~B1 || (A1 && C1)) && (~B2 || A2) && (~B2 || C2) &&...&& (~Bn || (An && Cn))) ||...|| 
		 * 		(An && (~B1 || (A1 && C1)) && (~B2 || (A2 && C2)) &&...&& (~Bn || An) && (~Bn || Cn))
		 * = ((~B1 || C1) && A1 && (~B2 || (A2 && C2)) &&...&& (~Bn || (An && Cn))) || 
		 * 		((~B1 || (A1 && C1)) && (~B2 || C2) && A2 &&...&& (~Bn || (An && Cn))) ||...|| 
		 * 		((~B1 || (A1 && C1)) && (~B2 || (A2 && C2)) &&...&& (~Bn || Cn) && An)		...X && (Y || X) = X
		 * = ((~B1 || (T && C1)) && A1 && (~B2 || (A2 && C2)) &&...&& (~Bn || (An && Cn))) || 
		 * 		((~B1 || (A1 && C1)) && (~B2 || (T && C2)) && A2 &&...&& (~Bn || (An && Cn))) ||...|| 
		 * 		((~B1 || (A1 && C1)) && (~B2 || (A2 && C2)) &&...&& (~Bn || (T && Cn)) && An)
		 * = (Fx(B -> (A && C)) && A1=T && A1) || (Fx(B -> (A && C)) && A2=T && A2) ||...|| (Fx(B -> (A && C)) && An=T && An)
		 * = (Fx(B -> (A && C)) && A1) || (Fx(B -> (A && C)) && A2) ||...|| (Fx(B -> (A && C)) && An)
		 * = Fx(B -> (A && C)) && (A1 || A2 ||...|| An)
		 * = ignoresDependency 
		 * 
		 * A && Fx(B -> (C && Fy(D -> A)))
		 * = Exy(A) && Fx(~B || (C && Fy(~D || A)))	...given A depends on ONLY x and y as Fxy
		 * = Exy(A) && Fx(~B || (C && (~Dy1 || Ay1) && (~Dy2 || Ay2) &&...&& (~Dym || Aym)))
		 * = ignoresDependency
		 */
		final ReductionOctet roAnd = new ReductionOctet(
				"A && Fx(B -> (A && C)) = ignoresDependency\n" +
				"A && Fx(B -> (C && Fy(D -> A))) = ignoresDependency",
				Operator.And, (Bconsq, c)-> equals(c), null, 
				(Bconsq, newC) -> ignoreDependency(Operator.And, p2));
		ros.add(fapImply);
		ros.add(roAnd);
		ros.add(fa);
		ros.add(fapImply);
		result = fap.reduceByOperands(ros, false);
		if (result != null) return result;
		
		fs.clear(); fs.add(p2);
		ros.clear();
		/*
		 * A && Fx(B -> Fy(C -> (A && D)))
		 * = Exy(A) && Fx(~B || Fy(~C || (A && D)))	...given A depends on ONLY x and y as Fxy
		 * = Exy(A) && Fx(~B || ((~Cy1 || (Ay1 && Dy1)) && (~Cy2 || (Ay2 && Dy2)) &&...&& (~Cym || (Aym && Dym))))
		 * = ignoresDependency
		 * 
		 * A && Fx(Fy(B -> A)) = Fx(Fy(B -> A)) && A
		 */
		ros.add(fapImply);
		ros.add(fa);
		ros.add(fapImply);
		ros.add(roAnd);
		return fap.reduceByOperands(ros, true);
	}
	
	/**
	 * @param fa - the relative beginning for matching Forall
	 * @param fs
	 * @return p2 if matched this; null if not
	 */
	private Proposition andByReduceForallAnd(Forall fa, List<Forall> fs) {
		final ReductionOperations ros = new ReductionOperations();
		/*
		 * A && Fx(B && Fy(C && Fz(D && Fw(E && A)))) 
		 * = A && Fx(B && Fy(C && Fz(D && Fw(E)))) && A		...given A independs on x, y, z and w 
		 * = A && Fx(B && Fy(C && Fz(D && Fw(E)))) 
		 */
		ros.addPrimDisj(new ReductionOctet(
				"A && Fx(B && Fy(C && Fz(D && Fw(E && A)))) = p2	...given A depends on ONLY x, y, z and w as Fxyzw",
				Operator.And, (X, b)-> equals(b), null, null, 
				(X, newX) -> dependsOnTheSame(fs) ? fa : null),
				new ReductionOctet(
				"A && Fx(B && Fy(C && Fz(D && Fw(E && A)))) = A && Fx(B && Fy(C && Fz(D && Fw(E))))...given A independs on x, y, z and w",
				Operator.And, (X, b)-> equals(b), null, null, 
				(X, newX) -> independsOn(fs) ? And.from(newX) : null));
		ros.add(Predicate.Operator.Forall, null, null, null, 
				(Fx, newX) -> ros.isReduced(0, 0) ? fa : 
					(ros.isReduced(0, 1) ? Forall.from(((Forall) Fx).quantifiers, newX.get(0)) : 
						andByReduceForallAnd((Forall) Fx, (List<Forall>) add(fs, fa))));
		// TODO? returnTodoException("ignoreDependency(Operator.And, p2)")
		// extracting the common and(()->...) from roForall
		try {
			return applySkipNull(result-> and(()-> result), ()-> fa.getProposition().reduceByOperands(ros, true));
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	
//	final protected Proposition andByReduceP2(Proposition p2) {
//		Relation.Operator op2 = p2.getOp();
//		
//		if (op2 instanceof Operator) switch ((Operator) op2) {
//		case And: 	return andByReduce((And) p2);
//		case Or: 	return andByReduce((Or) p2);
//		case Imply: return andByReduce((Imply) p2);
//		case Not: 	return andByReduce((Not) p2);
//		case True:	return andByReduce((True) p2);
//		case False: return andByReduce((False) p2);
//		case FunctionCall:
////		case Iff:
////		case Xor:
//		default:
//		}
//		
//		if (op2 instanceof Predicate.Operator) return andByReduce((Predicate) p2);
//		
//		return null;
//	}
	
	
	
	final public Proposition or(final Proposition p2)	{
		return or(()-> p2);
	}
	
	/**
	 * <pre>
	 * Guard for any pre-/post-processing.
	 * 
	 * TODO: mergeLocals(newProp.locals);
	 * TODO: (Forall)
	 * 
	 * @param p2
	 * @return
	 */
	final public Proposition or(Supplier<Proposition> p2)	{
		return Or.from(this, p2);
	}
	
	/**
	 * Guard method for any pre-/post-processing.
	 * Linearization during optimization saves hashing time.
	 * 
	 * @param p2s
	 * @return
	 */
	final public Proposition or(List<Proposition> p2s) {
		return or(()-> Or.from(p2s));
	}
	
//	final public Proposition or(Set<Proposition> p2s) {
//		if (p2s == null || p2s.isEmpty()) {
//			Debug.throwInvalidityException("Empty p2's?");
//			return null; 
//		}
//		return or(new ArrayList<>(p2s));
//	}
	
	final public Proposition orSkipNull(final Proposition p2) {
		return p2 == null ? this : or(()-> p2);
	}
	
	/**
	 * For separated and precise Proposition/Predicate sub-type and handling.
	 * 
	 * @param newProp
	 * @return
	 */
	protected Proposition orByReduce(Proposition p2) {
		return null;
	}
	
	private Proposition orByReduce(And p2) {
		final ReductionOperations ros = new ReductionOperations();
		/*
		 * A \/ (B /\ A)
		 * = A
		 */
		final ReductionOctet and = new ReductionOctet("A || (B && A) = A",
				null, (p2_, b)-> equals(b), null, 
				(p2_, newB)-> ros.isReduced(0) ? this : or(()-> And.from(newB)));
		ros.add(and);
		/*
		 * A \/ (B /\ (C \/ A))
		 * = (A \/ B) /\ (A \/ C \/ A)
		 * = (A \/ B) /\ (A \/ C)
		 * = A \/ (B /\ C)
		 */
		ros.add("A || (B && (C || A)) = A || (B && C)",
				Operator.Or, (b, c)-> equals(c), null, (b, newC)-> Or.from(newC));
		/*
		 * A \/ (B /\ (C \/ (D /\ A)))
		 * = (A \/ B) /\ (A \/ C \/ (D /\ A))
		 * = (A \/ B) /\ (A \/ C \/ D) /\ (A \/ C \/ A)
		 * = (A \/ B) /\ (A \/ C \/ D) /\ (A \/ C)
		 * = (A \/ B) /\ (A \/ C)	...(X \/ Y) /\ X = X
		 * = A \/ (B /\ C)
		 * 
		 */
		final String rule = "A || (B && (C || (D && A))) = A || (B && C)";
		ros.add(rule, Operator.And, (c, d)-> equals(d), null, (c, newD)-> False.from(rule, Operator.Or, this, p2));
		/*
		 * A || (B && (C || ((A || E) && D)))
		 * = A || (B && (C || (A && D) || (E && D)))
		 * = A || (B && C) || (B && A && D) || (B && E && D)
		 * = A || (B && C) || (B && E && D)		...X || (X && Y) = X
		 * = A || (B && (C || (E && D)))
		 */
		ros.add("A || (B && (C || ((A || E) && D))) = A || (B && (C || (E && D)))",
				Operator.Or, (d, e)-> equals(e), null, (d, newE)-> Or.from(newE));
		Proposition result = p2.reduceByOperands(ros, false);
		if (result != null) return result;

		/*
		 * A || (B && Fx(C -> A))
		 * = Ex(A) || (B && Fx(~C || A))	...given A depends on ONLY x as Fx
		 * = A1 || A2 ||...|| An || (B && (~C1 || A1) && (~C2 || A2) &&...&& (~Cn || An))
		 * = (A1 || A2 ||...|| An || B) && (A1 || A2 ||...|| An || ~C1) && (A1 || A2 ||...|| An || ~C2) 
		 * 		&&...&& (A1 || A2 ||...|| An || ~Cn)
		 * = (A1 || A2 ||...|| An) || (B && ~C1 && ~C2 &&...&& ~Cn)
		 * = A || (B && Fx(~C))
		 */
		final List<Forall> fas = new ArrayList<>();
		final ReductionOctet fa = new ReductionOctet(
				"A || (B && Fx(C -> A)) = A || (B && Fx(~C))	...given A depends on ONLY x as Fx",
				Predicate.Operator.Forall, (Fx, X)-> !fas.add((Forall) Fx), null,  
				(Fx, newX) -> Forall.from(((Forall) Fx).getQuantifiers(), newX.get(0))),
		ic = new ReductionOctet(Operator.Imply, 
				(X, XI)-> equals(((Imply) XI).consequent) && dependsOnTheSame(fas), null, 
				(X, newXI) -> ((Imply) X).antecedent.not());
		ros.clear();
		ros.add(and);
		ros.add(fa);
		ros.add(ic);
		return p2.reduceByOperands(ros, false);
	}
	
	/**
	 * A \/ (A \/ B) = A \/ B
	 * 
	 * A \/ ((C /\ A) \/ B)
	 * = A \/ (C /\ A) \/ B
	 * = A \/ B		... X\/(X/\Y) = X
	 * 
	 * @param p2
	 * @return
	 */
	private Proposition orByReduce(Or p2) {
		boolean isReduced = false;
		List<Proposition> B = new ArrayList<>();
		B: for (Proposition b : p2.getPropositions()) {
			// A \/ (A \/ B) = A \/ B
			if (equals(b)) return p2;
			
			// A \/ ((C /\ A) \/ B) = A \/ B
			if (b.getOp() == Operator.And) 
				for (Proposition c : b.getPropositions())
					if (equals(c)) {isReduced = true; continue B;}
			B.add(b);
		}
		return isReduced 
				? (B.isEmpty() ? this : or(()-> Or.from(B))) 
				: null;
	}
	
	/**
	 * DeMorgan's Law:
	 * A \/ ~/\Bn
	 * = A \/ \/~Bn
	 * 
	 * @param p2
	 * @return
	 */
	private Proposition orByReduce(Not p2) {
		assert p2 != null;
		Proposition notNp = p2.not();
		
		// A \/ ~/\Bn = A \/ \/~Bn
		if (notNp.getOp() == Operator.And) {
			Proposition result = this;
			for (Proposition p : ((And) notNp).getPropositions())
				result = result.or(()-> p.not());
			return result;
		}
		return null;
	}
	
	/**
	 * A \/ T = T
	 * 
	 * @param p2
	 * @return
	 */
	private Proposition orByReduce(True p2) {
		return True.from(Operator.Or, this, p2);
	}
	
	/**
	 * A \/ F = A
	 * 
	 * @param newProp
	 * @return
	 */
	private Proposition orByReduce(False newProp) {
		return this;
	}
	
//	final protected Proposition orByReduceP2(Proposition newProp) {
//		Relation.Operator npOp = newProp.getOp();
//		if (npOp instanceof Operator) switch ((Operator) npOp) {
//		case And: 	return orByReduce((And) newProp);
//		case Or: 	return orByReduce((Or) newProp);
//		case Imply: return orByReduce((Imply) newProp);
//		case Not: 	return orByReduce((Not) newProp);
//		case True: 	return orByReduce((True) newProp);
//		case False: return orByReduce((False) newProp);
//		case FunctionCall:
//		default:
//		}
//		return null;
//	}
	
	
	
	/**
	 * @param p2
	 * @return
	 */
	final public Proposition xor(Supplier<Proposition> p2) {
		return returnTodoException("xor relation");
	}
	

	
	/**
	 * A guard to ensure both antecedent and consequent are optimized.
	 * Also a guard method for any pre-/post-processing.
	 * 
	 * flattening hierarchy:
	 * 
	 * A -> ~A
	 * = ~A \/ ~A
	 * = ~A
	 * 
	 * <br>
	 * <p> TODO: This is mutable ONLY for Imply. 
	 * (Mutable ones are limited to And/OrderRelation.and(...), Or.or(...), Imply.imply(...) 
	 * and Iff.iff(...) ONLY)
	 * 
	 * 
	 * @param p2
	 * @return
	 */
	final public Proposition imply(Supplier<Proposition> p2) {
		return Imply.get(this, p2);
	}
		
	/**
	 * For separated and precise Proposition/Predicate sub-type and handling.
	 * 
	 * @param p2
	 * @return
	 */
	protected Proposition implyByReduce(Proposition p2) {
		return null;
	}
	
	/**
	 * A factory delegate method to ensure both antecedent and consequent are optimized.
	 * 
	 * A -> (B /\ A)				A -> (B /\ (A -> C))
	 * = ~A \/ (B /\ A)				= A -> (B /\ (~A \/ C))
	 * = (~A \/ B) /\ (~A \/ A)		= A -> ((B /\ ~A) \/ (B /\ C))
	 * = ~A \/ B					= (~A \/ (B /\ ~A)) \/ (B /\ C)
	 * = A -> B						= ~A \/ (B /\ C)
	 * 								= A -> (B /\ C)
	 * 
	 * A -> (B /\ (C -> A))
	 * = ~A \/ (B /\ (~C \/ A))
	 * = ~A \/ (B /\ ~C) \/ (B /\ A)
	 * = (B /\ ~C) \/ ((~A \/ B) /\ (~A \/ A))
	 * = (B /\ ~C) \/ ~A \/ B
	 * = ((B \/ B) /\ (~C \/ B)) \/ ~A
	 * = (B /\ (~C \/ B)) \/ ~A
	 * = A -> B
	 * 
	 * A -> (B /\ ((D /\ A) -> C))
	 * = ~A \/ (B /\ (~(D /\ A) \/ C))
	 * = ~A \/ (B /\ (~D \/ ~A \/ C))
	 * = ~A \/ (B /\ ~D) \/ (B /\ ~A) \/ (B /\ C)
	 * = ~A \/ (B /\ ~D) \/ (B /\ C)
	 * = ~A \/ (B /\ (~D \/ C))
	 * = A -> (B /\ (D -> C))
	 * 
	 * A -> (B /\ (C -> (D /\ A)))
	 * = ~A \/ (B /\ (~C \/ (D /\ A)))
	 * = ~A \/ (B /\ (~C \/ D) /\ (~C \/ A))
	 * = (~A \/ B) /\ (~A \/ ~C \/ D) /\ (~A \/ ~C \/ A)
	 * = (~A \/ B) /\ (~A \/ ~C \/ D)
	 * = ~A \/ (B /\ (~C \/ D))
	 * = A -> (B /\ (C -> D))
	 * 
	 * A -> (B /\ ForallA)
	 * = ~(A0\/A1\/...\/An) \/ (B /\ [A0/\A1/\.../\An])
	 * = (~A0/\~A1/\.../\~An) \/ (B /\ [A0/\A1/\.../\An])												   X:A0/\A1		Y:~A0/\~A1
	 * = [(~A0/\~A1/\.../\~An) \/ B] /\ [(~A0/\~A1/\.../\~An) \/ (A0/\A1/\.../\An)]	... A0 A1 ... An | /\.../\An	/\.../\~An	X\/Y
	 * = ignoresDependency																0  0  ... 0  | 0			1			1
	 * 																					0  0  ... 1  | 0			0			0
	 * 																						  ...
	 * 																					0  1  ... 0  | 0			0			0
	 * 																						  ...
	 * 																					1  1  ... 1  | 1			0			1
	 * A -> (B /\ Forall(A -> C))
	 * = ~A \/ (B /\ Forall(~A \/ C))
	 * = (~A \/ B) /\ [~A \/ Forall(~A \/ C)]
	 * = (~A \/ B) /\ [~(A0\/A1\/...\/An) \/ [(~A0\/C0)/\(~A1\/C1)/\.../\(~An\/Cn)]]
	 * = (~A \/ B) /\ [(~A0/\~A1/\.../\~An) \/ [(~A0\/C0)/\(~A1\/C1)/\.../\(~An\/Cn)]]
	 * = (~A \/ B) /\ [(~A0/\~A1/\.../\~An) \/ (~A0\/C0)] /\ [(~A0/\~A1/\.../\~An) \/ (~A1\/C1)] /\
	 * 		.../\ [(~A0/\~A1/\.../\~An) \/ (~An\/Cn)]							(X/\Y) 			(~X/\Y) 
	 * = (~A \/ B) /\ (~A0\/C0) /\ (~A1\/C1) /\ ... /\ (~An\/Cn)	... X Y Z | \/X\/Z = X\/Z	\/(X/\Z)
	 * = (A -> B) /\ (A0->C0) /\ (A1->C1) /\ ... /\ (An->Cn)			0 0 0 | 0 				0
	 * = (A -> B) /\ Forall(A -> C)										0 0 1 | 1 				0
	 * 																	0 1 0 | 0 				1
	 * 																	0 1 1 | 1 				1
	 * 																	1 0 0 | 1 				0
	 * 																	1 0 1 | 1 				1
	 * 																	1 1 0 | 1 				0
	 * 																	1 1 1 | 1				1
	 * = [(~A0/\~A1/\.../\~An) \/ B] /\ (~A0\/C0) /\ (~A1\/C1) /\ ... /\ (~An\/Cn) 
	 * = (~A0\/B) /\ (~A1\/B) /\ ... /\ (~An\/B) /\ (~A0\/C0) /\ (~A1\/C1) /\ ... /\ (~An\/Cn)
	 * = A -> (B /\ Forall x A(x) -> C(x))
	 * = Exists x A(x) -> (B /\ Forall x A(x) -> C(x))
	 * 		??[(~Forall x A(x) -> C(x)) -> Forall x A(x) -> Exists x A(x) ->
	 * 		 ~(Exists x A(x) -> (B /\ Forall x A(x) -> C(x)))]
	 * = B /\ Forall x A(x) -> C(x)
	 * 
	 * @param p2
	 * @return
	 */
	private Proposition implyByReduce(And p2) {
		boolean isReduced = false;
		List<Proposition> B = new ArrayList<>();
		for (Proposition b : p2.getPropositions()) {
			if (!isReduced) {
				// A -> (B /\ A) = A -> B						
				if (b.equals(this)) {isReduced = true; continue;}
				
				final Relation.Operator bOp = b.getOp();
				if (bOp.equals(Operator.Imply)) {
					Imply bi = (Imply) b;
					List<Proposition> D = new ArrayList<>();
					Proposition bia = bi.antecedent, bic = bi.consequent;
					// A -> (B /\ (A -> C)) = A -> (B /\ C)
					if (bia.equals(this)) {
						b = bic; isReduced = true;
					} 
					// A -> (B /\ (C -> A)) = A -> B
					else if (bic.equals(this)) {
						isReduced = true; continue;
					} 
					// A -> (B /\ ((D /\ A) -> C)) = A -> (B /\ (D -> C))
					else if (bia.getOp() == Operator.And) {
						for (Proposition d : ((And) bia).getPropositions()) {
							if (d.equals(this)) isReduced = true;
							else D.add(d);
						}
						if (isReduced) b = And.from(D).imply(()-> bic);
					}
					// A -> (B /\ (C -> (D /\ A))) = A -> (B /\ (C -> D))
					else if (bic.getOp() == Operator.And) {
						for (Proposition d : ((And) bic).getPropositions()) {
							if (d.equals(this)) isReduced = true;
							else D.add(d);
						}
						if (isReduced) b = bia.imply(()-> And.from(D));
					}
					
				} else if (bOp.equals(Predicate.Operator.Forall)) {
					/*
					 * A -> (B && Fx(A)) 
					 * = Ex(A) -> (B && Fx(A))	...given A depends on ONLY x
					 * = ~(A1 || A2 ||...|| An) || (B && A1 && A2 &&...&& An)
					 * = (~A1 && ~A2 &&...&& ~An) || (B && A1 && A2 &&...&& An)	...(~X && ~Y) || X = (~X || X) && (~Y || X) = Y->X
					 * = ignoresDependency
					 * 
					 * A -> (B && Fx(A -> C)) 
					 * = ~Ex(A) || (B && Fx(~A || C))	...given A depends on ONLY x 
					 * = ~(A1 || A2 ||...|| An) || (B && (~A1 || C1) && (~A2 || C2) &&...&& (~An || Cn)) 
					 * = (~A1 && ~A2 &&...&& ~An) || (B && (~A1 || C1) && (~A2 || C2) &&...&& (~An || Cn))
					 * = ignoresDependency 
					 * ??= (A -> B) /\ Forall(A -> C)
					 * 
					 * A -> (Fx(C -> Fy(A -> D)) && B)
					 * = Exy(A) -> (Fx(C -> Fy(A -> D)) && Exy(B))	...given A depends on ONLY x and y
					 * = ~Exy(A) || (Fx(~C || Fy(~A || D)) && Exy(B))
					 * = ignoresDependency
					 */
					final ReductionOperations ros = new ReductionOperations();
					ros.addPrimDisj(new ReductionOctet("A -> (B && Fx(A)) = ignoresDependency",
							null, (X, a)-> equals(X), null, null, 
							(X, newA) -> {ignoreDependency(Operator.Imply, p2); return null;}),
					new ReductionOctet("A -> (B && Fx(A -> C)) = ignoresDependency",
							Operator.Imply, (X, ac)-> equals(((Imply) X).antecedent), 
							null, (X, ac)-> ((Imply) X).consequent, 
							(X, newAC) -> {ignoreDependency(Operator.Imply, p2); return null;}));
					ros.add("A -> (Fx(C -> Fy(A -> D)) && B) = ignoresDependency",
							Predicate.Operator.Forall, null, null, null);
					// ignoresDependency doesn't need to return
					((Forall) b).getProposition().reduceByOperands(ros, true);	
				}
			}
			B.add(b);
		}
		
		// doing the rest optimization if not isReduced
		return isReduced ? imply(()-> And.from(B)) : null;
	}
	
	/**
	 * Flattening hierarchy:
	 * 
	 * A -> (B \/ C)
	 * = ~A \/ (B \/ C)
	 * = ~A \/ B \/ C
	 * 
	 * @param p2
	 * @return
	 */
	private Proposition implyByReduce(Or p2) {
		assert p2 != null;
		return p2.or(()-> not());
	}
	
	/**
	 * Flattening hierarchy:
	 * 
	 * 嚜澤 -> (B -> C)			嚜澤 -> (/\Bn -> C)
	 * = ~A \/ (~B \/ C)		= ~A \/ (~(/\Bn) \/ C)
	 * = ~A \/ ~B \/ C			= ~A \/ (\/(~Bn) \/ C)
	 * = ~(A /\ B) \/ C			= \/(~A, (~Bn), C)
	 * = (A /\ B) -> C			= \/(~A, (~Bn)) \/ C)
	 * 							= ~/\(A, (Bn)) \/ C
	 *							= /\(A, (Bn)) -> C 
	 * @param p2
	 * @return
	 */
	private Proposition implyByReduce(Imply p2) {
		assert p2 != null;
		return and(()-> p2.antecedent).imply(()-> p2.consequent);
	}
	
	/**
	 * A -> T = T
	 * 
	 * @param p2
	 * @return
	 */
	private Proposition implyByReduce(True p2) {
		return True.from(Operator.Imply, this, p2);
	}
	
//	/**
//	 * @param p2
//	 * @return
//	 */
//	private Proposition implyByReduceGeneral(False p2) {
//		return p2;
//	}
	
	/**
	 * Flattening hierarchy:
	 * 
	 * A -> ~B
	 * = ~A \/ ~B
	 * = ~(A /\ B)
	 * 
	 * @param p2
	 * @return
	 */
	private Proposition implyByReduce(Not p2) {
		assert p2 != null;
		return and(()-> p2.not()).not();
	}
	
	/**
	 * A -> Forall(A -> B)
	 * = ~A \/ Forall(~A \/ B)
	 * = ~(A0\/A1\/...\/An) \/ [(~A0\/B0)/\(~A1\/B1)/\.../\(~An\/Bn)]
	 * = [(~A0/\~A1/\.../\~An) \/ (~A0\/B0)] /\ [(~A0/\~A1/\.../\~An) \/ (~A1\/B1)] /\.../\
	 * 		[(~A0/\~A1/\.../\~An) \/ (~An\/Bn)]
	 * = (~A0\/B0) /\ (~A1\/B1) /\.../\ (~An\/Bn)	... (X/\Y) \/ X\/Z = X\/Z
	 * = Forall(A -> B)
	 * 
	 * @param p2
	 * @return
	 */
	private Proposition implyByReduce(Predicate p2) {
		if (p2.getOp() == Predicate.Operator.Forall) {
			Proposition fp = p2.getProposition();

			// A -> Forall(A -> B) = Forall(A -> B)
			if (fp.getOp() == Operator.Imply && equals(((Imply) fp).antecedent)) return p2;
		}
		return null;
	}
	
	
	
	/**
	 * @param p2
	 * @return
	 */
	final public Proposition iff(Supplier<Proposition> p2) {
		return Iff.from(this, p2);
	}
	
	/**
	 * For separated and precise Proposition/Predicate sub-type and handling.
	 * 
	 * This method is left override-able for {@link True} and {@link False}.
	 * 
	 * @param p2
	 * @return
	 */
	protected Proposition iffByReduce(Proposition p2) {
		return null;
	}
	
//	/**
//	 * @param p2
//	 * @return A <-> (B -> C)
//	 * 	= (A -> (B -> C)) && ((B -> C) -> A)
//	 * 	= (~A || (~B || C)) && (~(~B || C) || A)
//	 * 	= (~A || ~B || C) && ((B && ~C) || A)
//	 * 	= (~A || ~B || C) && (B || A) && (~C || A)
//	 */
//	private Proposition iffByReduce(Imply p2) {
//		assert p2 != null;
//		return and(p2.antecedent).imply(()-> p2.consequent);
//	}
	
//	/**
//	 * @param p2
//	 * @return A <-> ~B 
//	 * 	= (A -> ~B) && (~B -> A) 
//	 * 	= (~A || ~B) && (B || A) 
//	 * 	= ((~A || ~B) && B) || ((~A || ~B) && A) 
//	 * 	= (~A && B) || (~B && B) || (~A && A) || (~B && A) 
//	 * 	= (~A && B) || (~B && A) 
//	 */
//	private Proposition iffByReduce(Not p2) {
//		assert p2 != null;
//		return and(()-> p2.not()).not();
//	}
	

	
	final public Proposition not() {
		if (not != null) return not;
		
		if (!enters(METHOD_NOT)) {
			enter(METHOD_NOT);
//			not = notByFunctionReduce();
//			if (not != null) return not;
			
//			not = debugCallDepth(()-> 
			not = debugCallDepth(PROP_CALL_DEPTH + 100, (Proposition) null, (Supplier<Proposition>) ()-> 
			notByReduce());
			leaveTotally(METHOD_NOT);
		}
		if (not != null) return not;

//		checkDependency(Operator.Not, this);
		return not = new Not(this);
//		return not.clone();
	}
		
	protected Proposition notByReduce() {
		return null;
	}

	@Override
	public Expression negate() {
		return not();
	}
	
	

	/* (non-Javadoc)
	 * @see ompca.vodcg.condition.Expression#unwrapOnce()
	 */
	@Override
	protected Expression reduceOnce() {
//		boolean isReduced = super.reduceOnce();	// faster reduction first
//		if (isReduced) return true;
		
//		if (getOp() == Operator.FunctionCall) ...;
		
		Proposition first = null, pToRemove = null;
		for (Proposition p : getPropositions()) {
			if (first == null) first = p;
			else if (p == first) {pToRemove = p; break;}	// avoiding equals(...)-reduce() cycle
		}
		if (pToRemove != null) {remove(pToRemove); return this;} 
		super.reduceOnce();
		return this;
	}
	
	
	
	/**
	 * DeMorgan's law:
	 * 
	 * ~(A \/ B)
	 * = ~A \/ ~B
	 * 
	 * ~(A <-> B)
	 * = ~((A -> B) /\ (B -> A))
	 * = ~((~A \/ B) /\ (~B \/ A))
	 * = ~(~A \/ B) \/ ~(~B \/ A)
	 * = (A /\ ~B) \/ (B /\ ~A)
	 * 
	 * @return 
	 */
	public List<Proposition> reduceByDeMorgan() {
		if (deMorgan != null) return deMorgan;
		
		final Iterable<Proposition> props = getPropositions();
		int notsCount = 0, propsCount = 0;
		// applying List-then-Set for conditional performance bottleneck
		List<Proposition> notProps = new ArrayList<>();	
		for (Proposition p : props) {
			Proposition notP = p.not();
			notProps.add(notP);
			if (notP.getOp() == Operator.Not) notsCount++;
			propsCount++;
		}
		deMorgan = notsCount < propsCount/2 ? notProps : Collections.emptyList();
		return deMorgan;
	}
	
	
	
	/**
	 * @param operations
	 * @param reducesRecursively
	 * @return
	 */
	final protected Proposition reduceByOperands(
			ReductionOperations operations, boolean reducesRecursively) {
		if (operations == null || operations.isEmpty()) return null;
		
		List<ReductionOctet> disj = operations.getDisjunction(0);
		for (ReductionOctet r : disj) try {
			assert disj != null;
			
			final Proposition probe = get(()-> r.getProbeTestingOp().apply(this), e-> this);
			final Relation.Operator rOp = r.getOp();
			if (rOp != null && probe.getOp() != rOp) continue;
				
			final List<Proposition> newOprds = new ArrayList<>();
			boolean isReduced = false;
			for (Proposition p : probe.getPropositions()) {
				if (!isReduced) {
					final Proposition p_ = p;
					if (isReduced |= get(()-> r.getTester().test(this, p_), e-> false)) {
						r.setResult(this);					// temporary result for isReduced() flag
						if (r.dropsTestingTrue()) continue;	// r.getInjectTestingTrue() == null
						else p = r.getInjectTestingTrue().apply(this, p);
					
					} else {								// depth-first-reduction 
						final Proposition ptfp = apply(r.getProbeTestingFalse(), ()-> this, ()-> p_, e-> p_);
						if (ptfp != this) {					// excluding self getPropositions()
							final Proposition rp = ptfp.reduceByOperands(
									operations.shiftReduce(reducesRecursively), 
									reducesRecursively);
							if (rp != null) {p = rp; isReduced = true;}
							// rp == null && r.isReduced() means dropsTestingTrue from sub-ops
							else if (isReduced = r.isReduced()) continue;	
						}
					}
				}
				newOprds.add(p);
			}
			
			if (isReduced || r.isReduced()) {
//				final Proposition result = debugCallDepth(2, null, ()-> Elemental.getSkipNull(()-> 
//				r.getReduceOperation().apply(this, newOprds)), newOprds);
				final Proposition result = debugCallDepth(PROP_CALL_DEPTH, (Proposition) null,  
						()-> Elemental.applySkipEmptyCol(
								newOs-> r.getReduceOperation().apply(this, newOs), ()-> newOprds));
				if (result == null) continue;
				r.setResult(result);
				return result;
			}

		} catch (Exception e) {
			throwUnhandledException(e);
		}
		return null;
	}
	
	
	
	private Proposition reduceByOp(Operator op, Proposition p2) {
		assert op != null && p2 != null;
		
		Proposition result = reduceByFunction(op, p2);
		if (result != null) return result;
		
		Relation.Operator op2 = p2.getOp();
		final boolean isP2Predicate = op2 instanceof Predicate.Operator;
		final boolean isP2PureProp = op2 instanceof Proposition.Operator;
		final Operator pop2 = isP2PureProp ? (Operator) op2 : null;
		switch (op) {
		case And:
			if (isP2Predicate) result = andByReduce((Predicate) p2);
			else if (isP2PureProp) switch (pop2) {
			case And: 	result = andByReduce((And) p2); 	break;
			case Or: 	result = andByReduce((Or) p2);		break;
			case Imply: result = andByReduce((Imply) p2);	break;
			case Not: 	result = andByReduce((Not) p2); 	break;
			case True:	result = andByReduce((True) p2); 	break;
			case False: result = andByReduce((False) p2);	break;
			case FunctionCall:								break;
			case Iff:
			case Xor:
			default:	
			}
			if (result == null) result = andByReduce(p2);
			break;
			
		case Or:
			if (isP2PureProp) switch (pop2) {
			case And: 	result = orByReduce((And) p2);		break;
			case Or: 	result = orByReduce((Or) p2);		break;
//			case Imply: result = orByReduce((Imply) p2);	break;
			case Not: 	result = orByReduce((Not) p2);		break;
			case True: 	result = orByReduce((True) p2);		break;
			case False: result = orByReduce((False) p2);	break;
			case FunctionCall:								break;
			default:
			}
			if (result == null) result = orByReduce(p2);
			break;
			
		case Imply:
			if (isP2Predicate) result = implyByReduce((Predicate) p2);
			else if (isP2PureProp) switch (pop2) {
			case And: 	result = implyByReduce((And) p2);	break;
			case Or: 	result = implyByReduce((Or) p2);	break;
			case Imply: result = implyByReduce((Imply) p2);	break;
			case Not: 	result = implyByReduce((Not) p2);	break;
			case True: 	result = implyByReduce((True) p2);	break;
//			case False: result = implyByReduce((False) p2);	break;
			case FunctionCall:								break;
			default:
			}
			if (result == null) result = implyByReduce(p2);
			break;
			
		case Iff:	
			if (isP2PureProp) switch (pop2) {
//			case Imply: result = iffByReduce((Imply) p2);	break;
//			case Not: 	result = iffByReduce((Not) p2);		break;
			default:
			}
			if (result == null) result = iffByReduce(p2);	
			break;
		
		case Xor:
		case Not:
		case True:
		case False:
		case FunctionCall:
		default:	returnTodoException("opByReduce(p2)?");	break;
		}
		
		// TODO: mergeLocals(newProp.locals);
		
		// (II)
//		if (getClass().equals(p2.getClass())) {
//			VOPCondGen.throwTodoException("Optimization?");
//		}
		return result;
	}
	
	
	
	/**<pre>
	 * When {@code prop} and {@code newProp} are in the same direct scope, 
	 * where 'direct' means no {@link CallProposition}'s are used, the 
	 * reduction is left for the normal various relations (/\, \/, -> and <->) 
	 * between {@code prop} and {@code newProp}:
	 * 
	 * 	Case I	 	- pScope(){prop} v.s. pScope(){newProp}   
	 * 		pScope(){prop} (/\ | \/ | -> | <->) pScope(){newProp}
	 * 		= pScope(){prop (/\ | \/ | -> | <->) newProp}
	 * 		See {@link #andReduced(Proposition)},
	 * 			{@link #orByReduce(Proposition)}),
	 * 			{@link #implyByReduce(Proposition)}) and
	 * 			{@link #iffByReduce(Proposition)}).
	 * 		
	 * Or when {@link CallProposition} is used as {@code prop}:
	 * 
	 * 	Case II		- pScope() v.s. pScope(){newProp}, where prop = pScope()   
	 * 		pScope() (/\ | \/ | -> | <->) pScope(){newProp}
	 * 		= pScope(),		if pScope() (/\ | \/ | -> | <->) newProp = pScope(),
	 * 		= ??pScope'(),	if pScope() (/\ | \/ | -> | <->) newProp = newProp,
	 * 		= ??pScope''(){prop (/\ | \/ | -> | <->) newProp},	otherwise.
	 * 		see {@link CallProposition#andReduced(Proposition)},
	 * 			{@link CallProposition#orByReduce(Proposition)},
	 * 			{@link CallProposition#implyByReduce(Proposition)} and
	 * 			{@link CallProposition#iffByReduce(Proposition)}.
	 * 
	 * 
	 * When {@code prop} and {@code newProp} are in different direct scopes and
	 * {@link CallProposition} is solely used in {@code newProp}, npScope()
	 * therefore is redundant and ignored like Case I and II: 
	 * 
	 * 	Case III	- pScope() v.s. npScope(){newProp:pScope()}, 
	 * 					where prop = pScope() and newProp = pScope() like Case II,
	 * 
	 * 	Case IV		- pScope(){prop} v.s. npScope(){newProp:pScope()},
	 * (See Case ?? at {@link ??} for [native] recursive calls)
	 * 	
	 * 		pScopeNative(){prop} 	(/\ | \/ | -> | <->) npScope(){newProp:pScopeNative()}	
	 * 		pScopeNonNative(){prop} 	(/\ | \/ | -> | <->) npScope(){newProp:pScopeNonNative()}	
	 * 		= (pScopeNative() | pScopeNonNative()){{body} = prop (/\ | \/ | <-> | -> ) {body}},
	 * 
	 * 		pScopeNative(){prop} 	(/\ | \/ | -> | <->) npScope(){newProp:pScopeNonNative()},
	 * 		pScopeNonNative(){prop} 	(/\ | \/ | -> | <->) npScope(){newProp:pScopeNative()}	
	 * 		= super.(and | or | imply | iff),
	 *  	See {@link #reduceByFunction(Operator, Proposition)},
	 *  
	 * Otherwise {@code newProp} can be reduced by a {@link CallProposition} as 
	 * what this method does:
	 * 
	 * 	Case V		- pScope() v.s. npScope(){newProp},
	 * 	Case VI		- pScope(){prop} v.s. npScope(){newProp},
	 * 		pScope(){prop} (/\ | \/ | -> | <->) npScope(){newProp:pScope()}
	 * 		= prop,		if prop (/\ | \/ | -> | <->) newProp = prop,
	 * 		= newProp,	if prop (/\ | \/ | -> | <->) newProp = newProp,
	 * 		= pScope(){prop (/\ | \/ | -> | <->) npScope()},	otherwise.
	 *  	See {@link #reduceByFunction(Proposition)},
	 *  		{@link #orByFunctionReduce(Proposition)},
	 *  		{@link #implyReduceByFunctions(Proposition)} and
	 *  		{@link #iffReduceByFunctions(Proposition)}.
	 * </pre>
	 * 
	 * @param op
	 * @param prop - An alternative to the object {@code this} to avoid possible 
	 * 	self modification in the instance methods of 
	 * 	{@link #andReduced(Proposition)},
	 * 	{@link #orByReduce(Proposition)},
	 * 	{@link #implyByReduce(Proposition)} and
	 * 	{@link #iffByReduce(Proposition)}.
	 * @param p2
	 * @param propRelNewProp - be sure not to modify {@link prop}
	 * @return
	 */
	private Proposition reduceByFunction(Operator op, Proposition p2) {
		assert op != null && p2 != null;
		
		Function scope = getFunctionScope(), scope2 = p2.getFunctionScope();
		switch (Function.compareIn(scope, scope2)) {
		case isAfter:	
			assert scope != null;
			if (VODCondGen.isGlobal(scope2) && scope.isMain()) break;

			/* scope2 calls scope: 
			 * scope2.addSideEffect/setBody(p2 op p1.callProposition)
			 * scope.addSideEffect/setBody(p1)
			 */
			if (scope2 != null) {
				Supplier<Proposition> p1cp = ()-> scope.toSideEffectCall(this, scope2),
						se2 = null;
				switch (op) {
				case And:	se2 = ()-> p2.and(p1cp);	break;
				case Or:	se2 = ()-> p2.or(p1cp);		break;
				case Imply:	se2 = ()-> p2.imply(p1cp);	break;
				case Iff:	se2 = ()-> p2.iff(p1cp);	break;
				case Xor:	se2 = ()-> p2.xor(p1cp);	break;
				case FunctionCall: returnTodoException("Call (p1, p2)?");break;
				case Not:
				case True:
				case False:
				default:	returnTodoException("Should NOT happen!");	break;
				}
				scope2.andSideEffect(se2);
			}
			return this;
		
		case isBefore:
			assert scope2 != null;
			if (VODCondGen.isGlobal(scope) && getNonNull(()-> scope2).isMain()) break;
			
			/* scope calls scope2: 
			 * scope.addSideEffect/setBody(p1 op p2.callProposition)
			 * scope2.addSideEffect/setBody(p2)
			 */
			Supplier<Proposition> p2cp = 
					()-> scope2.toSideEffectCall(p2, scope != null ? scope : getCondGen().getGlobalScope());
			switch (op) {
			case And:	return and(p2cp);
			case Or:	return or(p2cp);
			case Imply:	return imply(p2cp);
			case Iff:	return iff(p2cp);
			case Xor:	return xor(p2cp);
			case FunctionCall: return returnTodoException("Call (p1, p2)?");
			case Not:
			case True:
			case False:
			default:	return returnTodoException("Should NOT happen!");
			}

		case equals:
		default:
			break;
		}
		return null;
	}
	
//	private Proposition reduceByFunctions(Operator op, 
//			FunctionCall<BooleanFunction>.CallProposition newCallProp) {
//		assert newCallProp != null;
//		
//		Function pScope = getFunctionScope();
//		if (pScope != null) {
//			if (pScope.equalsFunction(newCallProp)) {
////			if (superRelPScopeP.equals(this)) 
////				return this;
////			if (superRelPScopeP.equals(newCallProp.getCallFunction().getBody())) 
////				return newCallProp;
//				return pScope.toSideEffectCall(op, this);
//			} else 
//				newCallProp.getCallFunction().checkCircularDependency(pScope);
//		}
//		return null;
//	}
	

	
	@Override
	protected void setDirty() {
		not = null;
		deMorgan = null;
//		setScope(getScope(), getFunctionScope());	// delayed and on-demand scope setting
//		PIC_PREFIX_CACHE.clear();
		super.setDirty();
	}
	
	
	
	public Iterable<Expression> getLocals() {
		return locals;
	}
	
	@Override
	public DataType getType() {
		return DataType.Bool;
	}
	
	
	
//	/* (non-Javadoc)
//	 * @see java.lang.Comparable#compareTo(java.lang.Object)
//	 */
//	@Override
//	public int compareTo(Proposition p2) {
//		if (p2 == null) 
//			VOPCondGen.throwNullArgumentException(new String[] {"p1", "p2"});
//		return toString().trim().hashCode() - p2.toString().trim().hashCode();
//	}
//
//	/* (non-Javadoc)
//	 * @see java.util.Comparator#compare(java.lang.Object, java.lang.Object)
//	 */
//	@Override
//	public int compare(Proposition p1, Proposition p2) {
//		if (p1 == null || p2 == null) 
//			VOPCondGen.throwNullArgumentException(new Object[] {p1, p2});
//		return p1.compareTo(p2);
//	}

	@Override
	protected boolean equalsToCache(SystemElement e2) {
		Proposition p2 = (Proposition) e2;
		if (getLocals() != p2.getLocals()) return false;
		return super.equalsToCache(p2);
	}
	
	@Override
	protected List<Integer> hashCodeVars() {
		List<Integer> vars = new ArrayList<>(super.hashCodeVars());
		vars.add(locals == null ? 0 : locals.hashCode());
		return vars;
	}


	
	static public boolean isMutexTrue(
			final IASTStatement stat, final VODCondGen condGen) {
		return stat instanceof IASTIfStatement 
				&& fromIfCondition((IASTIfStatement) stat, condGen).isTrue();
		
//		if (stat == null) throwNullArgumentException("node");
//
//		IASTIfStatement eif = ASTUtil.getEnclosingIfStatementOf(stat);
//		while (eif != null && eif.getElseClause() != null) {
//			final Proposition eifp = fromRecursivelyWithoutBranching(
//					eif.getConditionExpression(), condGen);
//			if (eifp.isTrue()) return true;
//			eif = ASTUtil.getEnclosingIfStatementOf(eif.getParent());
//		}
//		return false;
	}
	

	
	final public Proposition ignoreDependency(Operator op, Relation rel2) {
		super.ignoreDependency(op, rel2);
		return null;
	}
	
	static final public Proposition returnIndependencyException() {
		return returnTodoException("in-dependency");
	}

	static final public Proposition returnTodoException(String message) {
		return throwTodoException(message);
	}
	
	public Proposition toProposition() {
		return this;
	}

	
	
	@Override
	public String toZ3SmtString(
			boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs) {
		String cond = new String();
		
		if (locals != null) {
			cond += "(let (";
			for (ConditionElement local : locals) 
				cond += local.toZ3SmtString(false, false, isLhs);
			cond += ") ";
		}
		
		// no locals to take care of and subclasses SHOULD take over control
		cond += super.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition, isLhs);
		
		// printing guards
		final Set<ArithmeticGuard> guards = getArithmeticGuards();
		if (guards != null && !guards.isEmpty()) {
			cond = "(and " + cond;
			for (ArithmeticGuard guard : guards)
				cond += (" " + guard.toZ3SmtString(false, false, isLhs));
			cond += ")";
		}
		
		assert cond != null; return cond;	// cond should NOT be null here!
	}

}
