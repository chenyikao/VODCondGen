/**
 * 
 */
package ompca.vodcg;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.eclipse.cdt.core.dom.IName;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IBinding;
import org.eclipse.cdt.core.dom.ast.IFunction;
import org.eclipse.cdt.core.dom.ast.IVariable;
import org.eclipse.cdt.core.index.IIndex;
import org.eclipse.cdt.core.index.IndexFilter;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;

import ompca.vodcg.condition.Proposition;

/**
 * Variable-oriented directed acyclic graph (VOD) ::= 
 * accessing reference [callee/variable] | ((accessing path '|')* accessing path) 
 * 
 * accessing path ::=
 * (accessing edge '->' )+ accessing edge
 * 
 * accessing edge ::=
 * accessing reference [callee/variable] : ('(' accessing condition ')')? accessing function [caller]
 * 
 * @author Kao, Chen-yi
 *
 */
public class VariableOrientedDag extends SystemElement 
implements Comparable<VariableOrientedDag> {
//implements Iterable<Assignable> {

//	public enum AccessingStrategy {
//		FirstAccessing, FirstWriting
//	}

//	private static final IllegalArgumentException ILLEGAL_CALLEE_EXCEPTION = 
//			new IllegalArgumentException("Must provide a variable reference as a callee!");
	private static final IllegalArgumentException ILLEGAL_PATH_EXCEPTION = 
			new IllegalArgumentException("Must provide some reachable paths!");
	
	final private static Map<Assignable<?>, VariableOrientedDag> 	
	CACHE = new HashMap<>();
	

	
	/**
	 * Index (IIndexName) isn't reliable enough to always give a non-null answer 
	 * while the AST way can.
	 */
	// head function doing the accessing - caller (of assignable)
	private IASTFunctionDefinition caller;		
	private Proposition calleeCond;
	private Assignable<?> callee;		
	
	// callee (as haf)
	final private Set<VariableOrientedDag> callerTails = new HashSet<>();
	
	
	
	/**
	 * @param callee - head accessing reference, can refer to either a variable or a function
	 * @param tail - provided if {@link wRef} is a function call, or null
	 */
	private VariableOrientedDag(Assignable<?> callee, VODCondGen condGen) 
			throws ASTException {
		super(condGen);
		
		if (callee == null) throwNullArgumentException("callee");
		
		final IBinding calleeBind = callee.getBinding();
		if (calleeBind != null) {
			if (!(calleeBind instanceof IVariable || calleeBind instanceof IFunction)) 
				throwTodoException("unsupported callee");
			
//			if (calleeBind instanceof IVariable) validTail = null;
			
			/* headAccessingFunc == null or not instance of IFunction means that 
			 * accessRef is (in) a global declaration access
			 */
//			aFunc = aRefBind.getOwner();	// not available (return null) for function call - IFunction.getOwner()
//			if (aFunc == null || !(aFunc instanceof IFunction)) throw ILLEGAL_WREF_EXCEPTION;
		}

		if (callee.isDirectlyConditional()) {
			calleeCond = Proposition.fromParentBranchCondition(callee, null, condGen);
			if (calleeCond == null) throwTodoException("falsely conditional?");
			if (calleeCond.isFalse()) throwTodoException("unreachable callee");
		}
		
		this.callee = callee;
		caller = callee.getWritingFunctionDefinition();
	}



//	/**
//	 * Combining constructor allowing neither empty head nor tail.
//	 * 
//	 * @param head
//	 * @param tail
//	 */
//	private VariableOrientedDag(VariableOrientedDag head, VariableOrientedDag tail) {
//		super(head.getCondGen());	// assert head != null;
//		if (head.isEmpty() || tail == null || tail.isEmpty()) throw ILLEGAL_PATH_EXCEPTION;
//		
//		headAccessingRef = head.getHeadAccessingRef();
//		headAccessingCond = head.getHeadAccessingCond();
//		headAccessingFunc = head.getHeadAccessingFunc();
//		VariableOrientedDag headTail = head.getTails();
//		addTail(headTail == null ? tail : new VariableOrientedDag(headTail, tail));
//	}



//	public static VOPWritingPath getFirstWritingPathOf(IIndexName subject, IIndex projIndex) throws CoreException {
//	IIndexName wFunc = subject.getEnclosingDefinition();
//	VOPWritingPath head = new VOPWritingPath(wFunc, subject, null);
//	
//	if (wFunc == null) return head;		// means that wRef is global
//	else {
//		// for sub-call recursively
//		VOPWritingPath headingPath = getFirstWritingPathOf(
//				new ASTRuntimeLocationComputer(projIndex).getFirstCalleeOf(wFunc), projIndex);
//		headingPath.setTailPath(head);
//		return headingPath;
//	}
//	
//}

	/**
	 * @param callee
	 * @param condGen
	 * @return a non-null collection.
	 */
	@SuppressWarnings("deprecation")
	public static VariableOrientedDag from(Assignable<?> callee, VODCondGen condGen) 
			throws ASTException {
		if (callee == null) throwNullArgumentException("callee assignable");

		VariableOrientedDag vod = CACHE.get(callee);
		if (vod != null) return vod;
		
		// head path
		vod = new VariableOrientedDag(callee, condGen);
		if (vod.isMain()) return vod;
		
		// tail paths
		final IASTName callerName = ASTUtil.getNameOf(vod.caller);
//		final IBinding hafBind = hafName.resolveBinding();
//		TODO? while (true) {
//		try {
//		} catch (InterruptedException e) {
//			continue;
//		}
		final IIndex index = ASTUtil.getIndex(false);
		try {
			index.acquireReadLock();	// read-lock pattern on the IIndex
			
			final ASTAddressable rtAddr = callee.cacheRuntimeAddress();
			for (IBinding callerCalleeBind : index.findBindings(
					callerName.toCharArray(), false, IndexFilter.ALL, new NullProgressMonitor()))
				// caller is defined (or caller is called) in the other translation units
				if (callerCalleeBind instanceof IFunction) 
					for (IName callerCalleeName : index.findReferences(callerCalleeBind)) try {
						final IASTFileLocation callerCalleeLoc = callerCalleeName.getFileLocation();
						final VariableOrientedDag callerTail = from(
								ASTUtil.getNameFrom(
										new Path(callerCalleeLoc.getFileName()), 
										callerCalleeLoc.getNodeOffset(), 
										callerCalleeLoc.getNodeLength(), 
										false), 
								rtAddr,
								condGen);
						if (callerTail != null) vod.addValidTail(callerTail);
						
//							firstCalleePos = 
//									fCallee1stWP.getHeadCompletedLocation();
//							if (firstCalleePos < minPos) {
//								minPos = firstCalleePos;
//								firstWP = fCallee1stWP;
//							}
					} catch (IllegalArgumentException e) {	// including ASTException 
						continue;
					}
			
		} catch (Exception e) {
			throwUnhandledException(e);
		} finally {
			index.releaseReadLock();
		}
		
		CACHE.put(callee, vod); 
		return vod;
	}
	
	public static VariableOrientedDag from(IASTName callee, final ASTAddressable rtAddr, VODCondGen condGen) 
			throws ASTException {
		return from(Assignable.from(callee, rtAddr, condGen), condGen);
	}

//	public static VariableOrientedDag firstFrom(Assignable lv, VOPCondGen condGen) {
//		return firstFrom(lv.getName(), condGen);
//	}
	
//	/**
//	 * @param callee - the subject variable to be wrote in 
//	 * @return the first accessing path
//	 */
//	@SuppressWarnings("deprecation")
//	public static VariableOrientedDag firstFrom(IASTName callee, VOPCondGen condGen) {
//		if (callee == null) throwNullArgumentException("callee name");
//		
//		VariableOrientedDag firstAp = CACHE.get(callee);
//		if (firstAp != null) return firstAp;
//		
//		for (VariableOrientedDag calleePath : from(callee, condGen)) 
//			if (calleePath.isFirstAccessingPath()) {firstAp = calleePath; break;}
//		
//		CACHE.put(callee, firstAp); 
//		return firstAp;
	
//	VOPWritingPath tail = new VOPWritingPath(subject, null);
//	IFunction wFunc = tail.getHeadWritingFunc();
//	
//	if (wFunc == null) return tail;	// subject is global
//	else {							// or for sub-call recursively
//		VOPWritingPath headingPath = getFirstWritingPathOf(
//				new ASTRuntimeLocationComputer(projIndex).getFirstCalleeOf(tail));
//		headingPath.setTailPath(tail);
//		return new ASTRuntimeLocationComputer(projIndex).getFirstCalleePathOf(tail);headingPath;
//	}
	
	// IIndex doesn't work!
	
//	IIndex projIndex = subject.getTranslationUnit().getIndex();	// IASTTranslationUnit.getIndex() doesn't work!
	
	// IIndex.findNames(...) neither works!
//	IIndex index = CCorePlugin.getIndexManager().getIndex(CoreModel.getDefault().getCModel().getCProjects());
//	index.acquireReadLock();
//	try {
//		IIndexName iname = index.findNames(subject.resolveBinding(), IIndex.FIND_ALL_OCCURRENCES)[0];
//		ASTRuntimeLocationComputer.bind(subject, iname);
//		return getFirstWritingPathOf(iname, index);
//	} finally {
//		index.releaseReadLock();
//	}
//}



//	/**
//	 * For the target function F ({@link headAccessingFunc})'s callee reference F_ref:
//	 * 	Main function has no first accessing path.
//	 * 	If the caller of F_ref, FCaller, is main, then the first (or direct) F_ref is the 
//	 * 	first accessing path of F.
//	 * 	Else the first accessing path of F is the first accessing path of FCaller, which is 
//	 * 	FCaller_ref.
//	 * 
//	 * TODO: F ref is not a declaration and has an enclosing caller?
//	 * 
//	 * @return
//	 */
//	public VariableOrientedDag getFirstAccessingPath() 
//			throws CoreException, InterruptedException {
//		if (isFirstAccessingPath()) return this;
//		return firstFrom(headAccessingRef, getCondGen());
//	}



	public boolean isMain() {
		assert getCondGen() != null;
		return caller == null		// global declaration/definition
				|| getCondGen().isMainFunction(caller); 
	}



	/**
	 * @return the caller function
	 */
	public IASTFunctionDefinition getCaller() {
		return caller;
	}

	public Proposition getCalleeCond() {
		return calleeCond;
	}
	
	/**
	 * @return the callee assignable
	 */
	public Assignable<?> getCallee() {
		return callee;
	}

	

	/**
	 * @return the file location of callee
	 */
	public IASTFileLocation getCalleeFileLocation() {
		return callee.getFileLocation();
	}
	
	/**
	 * @return Semantic location in execution (calling) completion order, 
	 * 	where arguments go prior to their function call.
	 */
	public int getCalleeCompletedLocation() {
		final IASTFileLocation loc = callee.getBinding() instanceof IFunction 
				? ASTUtil.getAncestorOfAsUnless(callee.getTopNode(), 
						ASTUtil.AST_FUNCTION_CALL_EXPRESSION,
						ASTUtil.AST_STATEMENT_TYPE,
						false).getFileLocation()
				: callee.getFileLocation();
		return loc.getNodeOffset() + loc.getNodeLength();
	}
	
	/**
	 * @return callee's code offset in the source file.
	 */
	public int getCalleeOffset() {
		return getCalleeFileLocation().getNodeOffset();
	}
	


	/**
	 * @return callee's starting line number in the source file.
	 */
	public int getCalleeStartingLineNumber() {
		return getCalleeFileLocation().getStartingLineNumber();
	}
	


	/**
	 * @return a non-null vod set
	 */
	public Iterable<VariableOrientedDag> getTails() {
		return callerTails;
	}



	public boolean addTail(VariableOrientedDag tail) {
		if (tail == null) throwNullArgumentException("tail");

		return addValidTail(tail) && hasValidTails();
	}
	
	private boolean addValidTail(VariableOrientedDag tail) {
//		if (tail == null && getCondGen().isMainFunction(caller)) 
		return callerTails.add(tail);
	}



	public boolean hasTails() {
		return !callerTails.isEmpty();
	}
	
	public boolean hasValidTails() {
		final boolean hasT = hasTails();
		if (hasT && (caller == null || getCondGen().isMainFunction(caller))) 
			ASTRuntimeLocationComputer.throwIncomparableException(ILLEGAL_PATH_EXCEPTION);
		return hasT;
	}

	public boolean hasManyTails() {
		return callerTails.size() > 1;
	}
	


	/**
	 * compare(null, main/func2) < 0;
	 * compare(func1, main) = compare(tail1, main);
	 * 
	 * func1 == func2 -> compare(var1, var2);
	 * 	func1 == func2 means ref1 and ref2 are in the same function
	 * 	and translation unit (for globally called ref1/ref2)
	 * 	TODO: handling multiple references in a macro-expansion
	 * 
	 * func1 != func2 -> var1 != var2;
	 * func1 != func2 && call1 == call2 -> compare(tail1, tail2);
	 * func1 != func2 && call1 != call2 -> compare(path1, tail2) && compare(tail1, path2) 
	 */
	public int compareTo(VariableOrientedDag vod2) 
			throws IllegalArgumentException {
		if (vod2 == null) throwInvalidityException("Incomparable null path");
		if (vod2 == this) return 0;
		
		final IASTFunctionDefinition func1 = getCaller(), 
				func2 = vod2.getCaller();
		
		// compare(null, main/func2) < 0;
		final Integer cag = 
				ASTRuntimeLocationComputer.compareAsGlobal(func1, func2);
		if (cag != null) return cag;
		
		// func1 == func2 -> compare(var1, var2), including sequential semantics in global declaration
		final Assignable<?> ref1 = getCallee(), ref2 = vod2.getCallee();
		final boolean isR1R2 = ref1 == ref2;
//		final boolean isR1R2 = ref1.equals(ref2);
		if (ASTUtil.equals(func1, func2)) {	
			if (isR1R2) return 0;
			else {
				final Proposition cond1 = getCalleeCond(), 
						cond2 = vod2.getCalleeCond();
				final boolean isR1ur = cond1 != null && cond1.isFalse(),
						isR2ur = cond2 != null && cond2.isFalse();
				if (isR1ur && isR2ur) return 0;		// both unreachably equal
				if (isR1ur) return 1;				// ref1 unreachable
				if (isR2ur) return -1;				// ref2 unreachable
				// unconditional or possibly conditionally reachable
				return getCalleeCompletedLocation() - vod2.getCalleeCompletedLocation();
			}
		}

		// func1 != func2 -> var1 != var2
		else {
			if (isR1R2) throwInvalidityException("inconsistent assignable");

			// main or global declaration/definition
			final VODCondGen cg = getCondGen();
			final boolean isM1 = cg.isMainFunction(func1), 
					isM2 = cg.isMainFunction(func2),
					nt1 = !hasValidTails(), nt2 = !vod2.hasValidTails();
			if (nt1 && nt2) return caller == null ? -1 : 1;		// global < main, caller2 == main != null
			
			assert !(isM1 && isM2);
			final Iterable<VariableOrientedDag> tails1 = getTails(), 
					tails2 = vod2.getTails();
			if (nt1) return compareTo(tails2);					// main/global ? tail2
			if (nt2) return -vod2.compareTo(tails1);					// tail1 ? main2/global2
			
			// tail1 ? tail2
			if (!hasManyTails() && !vod2.hasManyTails()) 
				return tails1.iterator().next().compareTo(
						tails2.iterator().next());
			// vod1 ? vod2 = tail1..main1/global1 ? vod2;
			return -vod2.compareTo(tails1);
		}
		
//		throw new IllegalArgumentException(
//				"Incomparable function: " + ASTUtil.toStringOf(func2.getDeclarator().getName()));
	}
	
	/**
	 * @param vods2
	 * @return the distance of me and the most preceding vod2
	 * @throws IllegalArgumentException
	 */
	private int compareTo(Iterable<VariableOrientedDag> vods2) throws IllegalArgumentException {
		assert vods2 != null && vods2.iterator().hasNext();
		int result = Integer.MIN_VALUE;
		for (VariableOrientedDag vod2 : vods2) {
			result = Math.max(result, compareTo(vod2));
//			if (result2 == 0) {if (result == null) result = 0; else if (result != 0) 
//				ASTRuntimeLocationComputer.throwIncomparableException();}
//			else if (result2 < 0) {if (result == null) result = -1; else if (result > -1) 
//				ASTRuntimeLocationComputer.throwIncomparableException();}
//			else {if (result == null) result = 1; else if (result < 1) 
//				ASTRuntimeLocationComputer.throwIncomparableException();}
		}
//		assert result != null;
		return result;
	}
	
	
	
	@Override
	protected Boolean cacheConstant() {
		throwTodoException("constant vop");
		return null;
	}

	
	
	/**
	 * @return always false.
	 */
	public boolean isEmpty() {
		assert (callee != null && caller != null);
		return callee == null;	// || headAccessingFunc == null;
	}



//	@Override
//	public Iterator<Assignable> iterator() {
//		final List<Assignable> it = new ArrayList<>();
//		assert getHeadAccessingRef() != null;
//		it.add(getHeadAccessingRef());
//		
//		final VariableOrientedDag tail = getTails();
//		if (tail != null) for (Assignable rest : tail) it.add(rest); 
//		return it.iterator();
//	}



	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		String str = callee.getShortNameAddress() 
				+ (caller == null 
					? "" 
					: ("\n\t@ " + ASTUtil.getNameOf(caller) 
						+ ":" + ASTUtil.toLineLocationOf(caller)));
		
		if (hasTails()) {
			str += " -> ";
			final boolean isTMany = hasManyTails();
			final Iterator<VariableOrientedDag> tails = getTails().iterator();
			if (isTMany) str += "(";
			str += tails.next().toString();
			while (tails.hasNext()) 
				str += (" | " + tails.next().toString());
			if (isTMany) str += ")";
		}
		return str;
	}

}