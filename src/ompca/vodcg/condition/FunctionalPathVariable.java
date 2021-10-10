/**
 * 
 */
package ompca.vodcg.condition;

import org.eclipse.cdt.core.dom.ast.IASTArrayDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTArrayModifier;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;

import ompca.vodcg.ASTAddressable;
import ompca.vodcg.Assignable;
import ompca.vodcg.FunctionalAssignable;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.data.ArrayPointer;
import ompca.vodcg.condition.data.ArrayType;
import ompca.vodcg.condition.data.DataType;
import ompca.vodcg.condition.data.PointerType;

/**
 * For both function path variables and their arguments.
 * 
 * @author Kao, Chen-yi
 *
 */
public class FunctionalPathVariable extends PathVariable {

//	static private FunctionalPathVariable preversion = null;

	
	
//	private FunctionalPathVariable(
//			PathVariable pv, IASTArraySubscriptExpression subArray, LValue lv, 
//			UniversalVersion initVersion, Proposition sideEffect) 
//					throws CoreException, InterruptedException {
//		super(pv);
//		init(lv);
//		
//		assert (initVersion != null && subArray != null);
//		setVersion(subArray, 
//				new ArrayAccessVersion(this, subArray, initVersion.getLValue(), sideEffect));
//	}
	
//	private FunctionalPathVariable(
//			PathVariable pv, IASTArraySubscriptExpression subArray, LValue lv, 
//			ArrayAccessVersion version, Proposition sideEffect) 
//			throws CoreException, InterruptedException {
//		super(pv);
//		init(lv);
//
//		setVersion(subArray, (version == null) 
//				? new ArrayAccessVersion(this, subArray, pv.getVersion(null).getLValue(), sideEffect) 
//				: version);
//	}
	
	/**
	 * @param asn
	 */
	private FunctionalPathVariable(Assignable<FunctionalPathVariable> asn) {
		super(asn, null);
//		init();
	}
	

	
	/**
	 * The wrapper (pseudo) constructor for path variable.
	 * 
	 * @param lv
	 * @param pv
	 */
	private FunctionalPathVariable(PathVariable pv) {
		super(pv);
//		init();
	}



//	private void init() {
//		if (lv.isAssigned()) Debug.throwInvalidityException("should provide args");
//		reversion(PathVariableDelegate.from(lv), null);	
//	}
	
	/**
	 * TODO: ArrayPathVariableDiscover	extends ASTGenericVisitor
	 * TODO: SideEffectCollector		extends ASTGenericVisitor
	 * 
	 * @param subArray
	 * @param condGen
	 * @return
	 */
	public static FunctionalPathVariable fromRecursively(
			IASTArraySubscriptExpression subArray, final ASTAddressable dynaAddr, VODCondGen condGen) {
		if (subArray == null) throwNullArgumentException("array expression");
		
		try {
			final PathVariable pv = 
					ArrayPointer.fromRecursively(subArray, dynaAddr, condGen)
					.getVariable();
			return pv instanceof FunctionalPathVariable
					? (FunctionalPathVariable) pv
					: new FunctionalPathVariable(pv);
			
		} catch (Exception e) {
			return throwTodoException(e);
		}
	}

	/**
	 * @param declarator
	 * @param asn
	 * @param pv - pre-cached path variable if available
	 * @return
	 */
	public static FunctionalPathVariable from(final IASTArrayDeclarator declarator, 
			final Assignable<FunctionalPathVariable> asn, final PathVariable pv) {
		if (asn == null) throwNullArgumentException("assignable");
//		if (testsNot(asn.isFunctional())) throwTodoException("true array");
//		if (asn.isLoopIterator() && !asn.isArrayPointer()) 
//			throwNullArgumentException("array loop iterator");

		final FunctionalPathVariable apv = pv == null 
				? new FunctionalPathVariable(asn) 
				: (pv instanceof FunctionalPathVariable 
						? (FunctionalPathVariable) pv : new FunctionalPathVariable(pv));
				
		ArrayType at = null;
		if (declarator != null) {
			at = ((PointerType) DataType.from(declarator.getName())).toArrayType();
			for (IASTArrayModifier am : declarator.getArrayModifiers()) {
				IASTInitializerClause sizeExp = am.getConstantExpression();
				if (sizeExp != null) try {
					assert at != null;
					at.setSize((ArithmeticExpression) Expression.fromRecursively(
							sizeExp, asn.cacheRuntimeAddress(), asn.getCondGen()));
					at = (ArrayType) at.nextPointingType();
					
				} catch (ClassCastException e) {
					// at instanceof DataType at the last iteration;
				} catch (Exception e) {
					throwTodoException("unsupported sub-array accessing");
				}
			}
		}
		
		if (at != null) apv.setType(at);
		return apv;
	}
	
	/**
	 * @param asn
	 * @return an AST array PV or a virtual (non-AST) one 
	 * 	for some loop statement
	 */
	public static FunctionalPathVariable from(final FunctionalAssignable asn) {
		return from(null, asn, PathVariable.from(asn));
	}
	


//	public final static FunctionalPathVariable get(
//			IASTName ov, IASTArraySubscriptExpression exp) throws CoreException {
//		PathVariable pv = PathVariable.allPathVariables.get(ov);
//		if (pv == null) {
//			pv = new FunctionalPathVariable(ov, exp);
//			PathVariable.allPathVariables.put(ov, pv);
//		}
//		return (FunctionalPathVariable) pv;
//	}

//	public static PathVariable getIfParsingArray(PathVariable pv, LValue lv) 
//			throws CoreException, InterruptedException {
//		if (pv == null) return null;
//		
//		IASTArraySubscriptExpression subArray = Array.getSubArrayInParsing();
//		if (subArray == null) return pv;
//		
//		Version pvv = pv.getVersion(lv);
//		FunctionalPathVariable apv = (pvv instanceof UniversalVersion) 
//				? new FunctionalPathVariable(pv, subArray, lv, (UniversalVersion) pvv, null)
//				: new FunctionalPathVariable(pv, subArray, lv, (ArrayAccessVersion) pvv, null);
//		register(lv, apv);
//		return  apv;
//	}

//	public static PathVariablePlaceholder findVersion(
//			IASTArraySubscriptExpression exp, VODCondGen condGen) {
//		if (exp == null) throwNullArgumentException("expression");
//		
//		final FunctionalPathVariable apv = fromRecursively(exp, condGen);
//		return (apv != null) 
//				? apv.getVersion((IASTArraySubscriptExpression) exp) 
//				: null ;
//	}
//	
//	protected PathVariablePlaceholder getVersion(IASTArraySubscriptExpression exp) {
//		if (exp == null) throwNullArgumentException("expression");
//		return ArrayPointer.fromRecursively(exp, getCondGen())
//				.getTopPlaceholder();
//	}
		
	
	
//	public static void preversionWithDimension(IASTInitializerClause dimArg) {
//		if (preversion == null) preversion = new FunctionalPathVariable(dimArg);
//		else preversion.addDimension(dimArg);
//	}

//	static public void version(IASTName ov) {
//		FunctionalPathVariable apv = new FunctionalPathVariable(ov, preversion);
//		PathVariable.allPathVariables.put(ov, apv);
//		preversion = null;	// reset the temporary cache preversion
//	}
	
//	private void setVersion(IASTArraySubscriptExpression exp, Version vv) 
//			throws CoreException, InterruptedException {
//		if (exp != null && vv != null) {
//			LValue lv = vv.getLValue();
//			ARRAY_LV_CACHE.put(exp, lv);
//			reversion(null, lv, vv);
//		}
//	}
	

	
//	static public PathVariableDelegate 
//	versionFunctionallyWith(Assignable ov, IASTForStatement loop) {
//		// assuring PV is created before APV
//		return from(ov).reversionFunctionally(ov, loop);
//	}
	
//	/**
//	 * Re-versioning from APV versions to functional ones 
//	 * when this array appears in a new loop and depends it.
//	 * 
//	 * @param ov
//	 * @param loop
//	 * @return
//	 */
//	public PathVariableDelegate reversionFunctionally(
//			Assignable ov, IASTForStatement loop) {
//		if (ov == null) Debug.throwNullArgumentException("array path variable");
//		if (loop == null) Debug.throwNullArgumentException("loop");
//		
//		/* oldVer == null || oldVer !instanceof FunctionalVersion
//		 * 	-> first-time showing of OV l-value
//		 * oldVer != null 
//		 * 	-> OV is already written before the loop
//		 */
//		FunctionalVersion.from(ov, this, loop).checkUbiquitous();
//		
//		return PathVariableDelegate.from(ov, FunctionalPathVariable.from(ov), null);
//	}

}