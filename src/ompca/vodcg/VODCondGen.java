package ompca.vodcg;

import java.math.BigInteger;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.time.temporal.ChronoUnit;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.NavigableSet;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IFunction;
import org.eclipse.cdt.core.index.IIndex;
import org.eclipse.cdt.core.index.IIndexBinding;
import org.eclipse.cdt.core.index.IIndexName;
import org.eclipse.cdt.core.index.IndexFilter;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.swt.widgets.Display;

import ompca.DuoKeyMap;
import ompca.Elemental;
import ompca.TrioKeyMap;
import ompca.condition.SerialFormat;
import ompca.vodcg.condition.ConditionElement;
import ompca.vodcg.condition.Function;
import ompca.vodcg.condition.Function.Parameter;
import ompca.vodcg.condition.PathVariable;
import ompca.vodcg.condition.VODConditions;
import ompca.vodcg.condition.data.ArrayType;
import ompca.vodcg.condition.data.Char;
import ompca.vodcg.condition.data.DataType;
import ompca.vodcg.condition.data.FiniteNumberGuard;
import ompca.vodcg.condition.data.PlatformType;
import ompca.vodcg.condition.data.PointerType;

/**
 * Generating VOD conditions:
 * 	1. given path conditions PathCond = Cond
 * 	2. given a target variable, TV, and its target expression line position, TP
 * 	3. VOD Cond = getVODCond(TV, TP)
 * 		getVODCond(OV, P), given an observed variable, OV, and its observation expression line position, P, ::=
 * 			i. finding writing reference holder expressions (history) of OV, WRS, before P
 * 			ii. for each expression E of WRS :
 * 				1. for each rewritable OV self reference in E :
 * 					a. If E's inside independently constant-indexed (possibly nested) loop(s) L_Const :
 * 						i. PathCond ||= versioning OV by indices
 * 						ii. if OV is global (behind a function call F), PathCond ||= inserting versions with tag 
 * 							F and index-expansion
 * 					b. else if E's inside independently IV-indexed (possibly nested) loop(s) L_IV :
 * 						i. PathCond ||= functional versioning OV by inserting init. clos. and postconditions
 * 						ii. if OV is global, PathCond ||= inserting versions with tag F
 * 					c. else if E's inside other independently non-indexed (possibly nested) loop(s) L_NI :
 * 						i.	PathCond ||= functional versioning OV by inserting init. clos. and postconditions of 
 * 							counting indices (CI) implied with general loop break conditions, i.e. 
 * 							CI > variant_bound -> BreakCond
 * 						ii.	if OV is global, PathCond ||= inserting versions with tag F
 * 					d. else if E's inside elsewhere (including inside dependent loops) :
 * 						i. PathCond ||= versioning OV
 * 						ii. if OV is global, PathCond ||= inserting versions with tag F
 * 				2. else for each rhs dependent variable reference DV of OV in E : PathCond ||= getVODCond(DV, P)
 * 				3. else if E's behind a function call F by reference : building a corresponding Z3 function
 * 			iii. parallel conditions ParallelCond
 * 			iv. return ParallelCond || PathCond
 * 
 * @author Kao, Chen-yi
 *
 */
public class VODCondGen extends SystemElement 
implements Comparator<IASTForStatement> {

	final public static String LIB_OMPCA_SMT = "ompca/smt";
	final public static int MAX_NUM_THREADS = 10;
	
	final static private Map<IPath, VODCondGen> CG_CACHE = new HashMap<>();
	

	
	/**
	 * target variable
	 */
	private Assignable<?> tv = null;	// in l-value
//	private ICProject tvProject;
//	private IIndex tvIndex = null;	// IIndex/AST is changing overtime and not encouraged to keep!
//	private IPath tvPath = null;
	private IPath mainPath = null;

	final static private Map<SortedSet<Assignable<?>>, SortedSet<IASTForStatement>> 
	LH_CACHE = new HashMap<>();
	
//	private WritingHistoryObserver whObserver = null;
	final static private Map<PathVariable, NavigableSet<Assignable<? extends PathVariable>>> 
	WH_CACHE = new HashMap<>();
	
//	private static final Method METHOD_COMPUTE_WORK_OF = 
//			Elemental.getMethod(VODCondGen.class, "computeWorkOf", Assignable.class);
//	/**
//	 * Value 1 - index of lv being traversed;
//	 * Value 2 - number of lv's traversed.
//	 * Value 3 - TODO: for both parallel and path conditions
//	 */
//	final static private TrioValueMap<PathVariable, Integer, Integer, PathCondition> 
//	COND_PROGRESS_CACHE = new TrioValueMap<>();

	final private Set<String> DECL_CACHE = new HashSet<>();

	final private VODConditions conds = new VODConditions(null, this);

	/**
	 * L-value assigners are processed in near first-in-last-out order.
	 */
//	final private Stack<Assignable> processedRhs = new Stack<>();

	private LocalDateTime start;
	private Display display = null; 
	/**
	 * Since it is illegal to call beginTask on the same IProgressMonitor more than once, 
	 * the same instance of IProgressMonitor must not be passed to convert more than once.
	 * @see org.eclipse.core.runtime.SubMonitor#convert(IProgressMonitor)
	 */
	private SubMonitor rootMonitor = null; 
	private int workRemaining = 0; 
	private static String CacheProgress = "..."; 
	
	private static final DateTimeFormatter MONTH_DATE_TIME = DateTimeFormatter.ofPattern("MMdd'T'HH:mm:ss"); 
	
	private static final Map<SerialFormat, Set<String>> KEYWORD_POOL = new HashMap<>(); 
	private static final DuoKeyMap<ConditionElement, SerialFormat, String> SYMBOL_POOL = new DuoKeyMap<>();
	
	
	
	private VODCondGen(IPath mainPath, Display display) {
		super(null);
		init(mainPath, display);
	}
	
//	/**
//	 * @param tvPath - the path to target variable
//	 * @param mainPath 
//	 */
//	private VODCondGen(VariablePath tvPath, IPath mainPath, Display display) {
//		super(null);
//		init(mainPath, display);
//		setTargetVariable(tvPath);
//	}
	
	public static VODCondGen from(IPath mainPath, Display display) {
		VODCondGen cg = CG_CACHE.get(mainPath);
		if (cg == null) CG_CACHE.put(mainPath, cg = new VODCondGen(mainPath, display));
		return cg;
	}
	

	
	final public static String findSymbol(ConditionElement entity, SerialFormat format) {
		return SYMBOL_POOL.get(entity, format);
//		entity instanceof Reference 
//		? ((Reference<?>) entity).getSubject() 
//		: entity);
	}

	
	
	final public static boolean isAmbiguous(
			String keywordSymbol, SerialFormat format) {
		return isAmbiguous(null, keywordSymbol, format);
	}
	
	final public static boolean isAmbiguous(
			ConditionElement entity, String keywordOrSymbol, SerialFormat format) {
		if (keywordOrSymbol == null || keywordOrSymbol.isEmpty()) return true;
		
		// character pool checking
		if (keywordOrSymbol.length() == 1 && Char.isUsed(keywordOrSymbol.charAt(0))) 
			return true;
		
		// keyword pool checking
		if (entity == null) return isKeyword(format, keywordOrSymbol);
		
		// symbol pool checking
		String entitySym = findSymbol(entity, format);
		if (entitySym == null) {
			if (SYMBOL_POOL.containsValue(format, keywordOrSymbol)) return true;
			else {
				if (keywordOrSymbol.contains("null")) throwInvalidityException("unnecessary null");
				return SYMBOL_POOL.put(entity, format, keywordOrSymbol) != null;
			}
//					entity instanceof Reference 
//					? ((Reference<?>) entity).getSubject() : entity, 
//					originalSymbol);
		} else
			return !entitySym.equals(keywordOrSymbol);
	}
	
	final public static boolean isKeyword(SerialFormat format, String subject) {
		return Elemental.get(()-> KEYWORD_POOL.get(format).contains(subject),
				e-> false);
	}
	
	final public static boolean addKeyword(
			SerialFormat format, String... subjects) {
		if (subjects == null || subjects.length == 0) 
			throwNullArgumentException("subject");
		
		Set<String> formatPool = KEYWORD_POOL.get(format);
		if (formatPool == null) {
			formatPool = new HashSet<>();
			KEYWORD_POOL.put(format, formatPool);
		}
		
		boolean result = true;
		for (String subject : subjects) {
//			if (formatPool.contains(subject)) return throwTodoException("conflicting " + subject);
			result &= formatPool.add(subject);
		}
		return result;
	}
	
	final public boolean addDeclaration(final String decl) {
		if (decl == null || decl.isBlank()) throwNullArgumentException("declaration");
		return DECL_CACHE.add(decl.trim());
	}
	
	final public boolean containsDeclaration(final String decl) {
		return decl == null || decl.isBlank() 
				|| DECL_CACHE.contains(decl.trim());
	}
	


	@Override
	public VODCondGen getCondGen() {
		return this;
	}
	
	public ConditionElement getGlobalScope() {
		return conds;
	}
	
	
	
	private Function CEIL_FUNCTION			= null; 
//	private Function CEIL_GUARD_FUNCTION	= null; 
//	private static final String[] C_LIBRARIES = {"<typeid>", "<stdio.h>", "<stdlib.h>", "<string.h>", "<math.h>", "<omp.h>"}; 
	private static final Set<String> C_LIBRARIES = new HashSet<>(); 
	/**
	 * Map of <library, ID, function, definition>
	 */
	private static final TrioKeyMap<String, String, Function, String> 
	Z3_SMT_LIBRARY_FUNCTIONS 			= new TrioKeyMap<>();



	private void init(IPath mainPath, Display display) {
		resetPlatformDeclaration();
		reset();
		
		this.display = display;
		
		final Parameter DIVIDEND = new Parameter("dividend", DataType.Int), 
				DIVISOR = new Parameter("divisor", DataType.Int);
		CEIL_FUNCTION		= Function.from(LIB_OMPCA_SMT, "ceil", DataType.Int, this, DIVIDEND, DIVISOR); 
//		CEIL_GUARD_FUNCTION	= Function.from(LIB_OMPCA_SMT, "ceil_guard", DataType.Bool, this, DIVIDEND, DIVISOR); 
		/* ceil(x) = 	to_int(x) 		if x <= to_int(x),
		 * 				to_int(x) + 1 	if x > to_int(x).
		 * to_int as the function that maps each real number r to its integer part, 
		 * that is, to the largest integer n that satisfies (<= (to_real n) r)
		 * (http://smtlib.cs.uiowa.edu/theories-Reals_Ints.shtml)
		 * (https://en.wikipedia.org/wiki/Floor_and_ceiling_functions) 
		 */
		Z3_SMT_LIBRARY_FUNCTIONS.put(
				CEIL_FUNCTION.getLibrary(), CEIL_FUNCTION.getID(SerialFormat.Z3_SMT), CEIL_FUNCTION,
//				TODO? CEIL_FUNCTION.toZ3SmtString(false, false)
				"(define-fun ceil ((_1 Real)) Int (let ((_int1 (to_int _1))) \n" +
					"\t(ite (<= _1 _int1) _int1 (+ _int1 1))\n" + 
//					"\t(ite (<= _1 (to_Real _int1)) _int1 (+ _int1 1))\n" + 
//				"(define-fun ceil ((dividend Int)(divisor Int)) Int (ite \n" +
//						"\t(= (mod dividend divisor) 0)\n" +
//						"\t(div dividend divisor)\n" + 
//						"\t(+ (div dividend divisor) 1)\n" +
				"))");
//		Z3_SMT_LIBRARY_FUNCTIONS.put(
//				CEIL_FUNCTION.getLibrary(), CEIL_GUARD_FUNCTION.getID(SerialFormat.Z3_SMT), CEIL_GUARD_FUNCTION,
//				";avoiding intermediate overflow\n" +
//				"(define-fun ceil_guard ((dividend Int)(divisor Int)) Bool (and \n" +
//						"\t(div_guard dividend divisor)\n" +
//						"\t(mod_guard dividend divisor)\n" +
//						"\t(add_guard (div dividend divisor) 1)\n" +
//				"))");
		
		Z3_SMT_LIBRARY_FUNCTIONS.put("<typeid>", "sizeof_Void",	
				Function.from("<typeid>", "sizeof", DataType.Int, this, new Parameter("_1", DataType.Void)), 
				"(declare-fun sizeof (Void) Int)");

		final Parameter _1 = new Parameter("_1", DataType.Real), _2 = new Parameter("_2", DataType.Real);
		final Function fAbs = Function.from("<math.h>", "fabs", DataType.Real, this, _1);
		fAbs.addGuard(FiniteNumberGuard.fromNonNegative(fAbs.getCall(null, getGlobalScope())));
		Z3_SMT_LIBRARY_FUNCTIONS.put("<math.h>", "fabs_Real",	
				fAbs, "(define-fun fabs ((_1 Real)) Real (ite (< _1 0.0) (- _1) _1))");
		Z3_SMT_LIBRARY_FUNCTIONS.put("<math.h>", "log_Real",	
				Function.from("<math.h>", "log", DataType.Real, this, _1),
				"(declare-fun log (Real Real) Real)");
		Z3_SMT_LIBRARY_FUNCTIONS.put("<math.h>", "pow_Real_Real",	
				Function.from("<math.h>", "pow", DataType.Real, this, _1, _2),
				"(declare-fun pow (Real Real) Real)");
		Z3_SMT_LIBRARY_FUNCTIONS.put("<math.h>", "sqrt_Real",	
				Function.from("<math.h>", "sqrt", DataType.Real, this, _1),
				"(declare-fun sqrt (Real) Real)\n(assert (forall ((x Real)) (= x (^ (sqrt x) 2.0))))");
		
		// [mingw32] FILE * fopen (const char *filename, const char *opentype)
		// [msys64] FILE *	fopen (const char *__restrict _name, const char *__restrict _type);
		Z3_SMT_LIBRARY_FUNCTIONS.put("<stdio.h>", "fopen_Str_Str", 
				Function.from("<stdio.h>", "fopen", DataType.Pointer, this, 
						new Parameter("_1", DataType.String), new Parameter("_2", DataType.String)),
				"(declare-fun fopen (Str Str) Pointer)");
		// [msys64] int printf (const char *__format, ...)
		Z3_SMT_LIBRARY_FUNCTIONS.put("<stdio.h>", "printf_Str", 
				Function.from("<stdio.h>", "printf", DataType.Int, this, new Parameter("_1", DataType.String),
						new Parameter("_Varargs", ArrayType.from(DataType.Void, null))),
				"(declare-fun printf (Str PT) Int)");
		// [mingw32] int fscanf (FILE *stream, const char *template, ...)
		// [msys64] int	fscanf (FILE *__restrict, const char *__restrict, ...)
		Z3_SMT_LIBRARY_FUNCTIONS.put("<stdio.h>", "fscanf_pt_Void_Str", 
				Function.from("<stdio.h>", "fscanf", DataType.Int, this, 
						new Parameter("_1", DataType.Pointer), new Parameter("_2", DataType.String), 
						new Parameter("_Varargs", ArrayType.from((PlatformType) DataType.Pointer, null))),
				"(declare-fun fscanf (Pointer Str) Int)");
		
		// int __cdecl atoi(const char *_Str);
		Z3_SMT_LIBRARY_FUNCTIONS.put("<stdlib.h>", "atoi_Str", 
				Function.from("<stdlib.h>", "atoi", DataType.Int, this, new Parameter("_1", DataType.String)),
				"(declare-fun atoi (Str) Int)");
		// void *__cdecl malloc(size_t _Size); TODO: recording the argument size for computing memory bounds
		Z3_SMT_LIBRARY_FUNCTIONS.put("<stdlib.h>", "malloc_Int", 
				Function.from("<stdlib.h>", "malloc", DataType.Pointer, this, new Parameter("_1", DataType.Int)),
				"(declare-fun malloc (Int) PT)");

		// char 	*strcpy (char *__restrict, const char *__restrict);
		Z3_SMT_LIBRARY_FUNCTIONS.put("<string.h>", "strcpy_Str_Str", 
				Function.from("<string.h>", "strcpy", DataType.String, this, 
						new Parameter("_1", DataType.String), new Parameter("_2", DataType.String)),
				"(declare-fun strcpy (Str Str) Str)");
		
		Z3_SMT_LIBRARY_FUNCTIONS.put("<omp.h>", "omp_get_num_threads", 
				Function.from("<omp.h>", "omp_get_num_threads", DataType.Int, this),
				"(declare-fun omp_get_num_threads () Int)");
		Z3_SMT_LIBRARY_FUNCTIONS.put("<omp.h>", "omp_get_thread_num", 
				Function.from("<omp.h>", "omp_get_thread_num", DataType.Int, this),
				"(declare-fun omp_get_thread_num () Int)");

		addKeyword(SerialFormat.Z3_SMT, 
				"declare-const", "declare-datatypes", "declare-sort", "declare-fun", "define-fun",
				"ite", "iff", "assert");
		setMain(mainPath);
	}
	
//	static {
//	}
	
	
	
	@SuppressWarnings("unused")
	private Display getDisplay() {
		if (display == null) display = Display.getCurrent();
		//may be null if outside the UI thread
		if (display == null) display = Display.getDefault();
		if (display == null) throwNullArgumentException("display");
		return display;		
	}

	public static String getID(Function f) {
		if (f == null) throwNullArgumentException("function");
		if (Z3_SMT_LIBRARY_FUNCTIONS.isEmpty()) throwTodoException("not-yet initialized");
		return getNonNull(()-> Z3_SMT_LIBRARY_FUNCTIONS.key2For(f));
	}
	
	public Function getCeilFunction() {
		return CEIL_FUNCTION;
	}
	
//	public Function getCeilGuardFunction() {
//		return CEIL_GUARD_FUNCTION;
//	}
	
	public static Set<String> getCLibraries() {
		if (C_LIBRARIES.isEmpty())
			for (String lib : Z3_SMT_LIBRARY_FUNCTIONS.key1Set())
				if (lib.startsWith("<") && lib.endsWith(">")) C_LIBRARIES.add(lib);
		return C_LIBRARIES;
	}
	
	public static Function getCLibraryFunction(String nameParams) {
		if (nameParams == null) return null;
		
		for (String lib : getCLibraries()) {
			Map<Function, String> libFuncs = Z3_SMT_LIBRARY_FUNCTIONS.get(lib, nameParams);
			if (libFuncs != null) for (Function f : libFuncs.keySet()) {
				if (f == null) throwTodoException("No such function: " + nameParams);
				return f;
			}
		}
		return null;
	}
	
	public Function getSmtLibraryFunction(String name) {
//		return getPlatformLibraryFunction("ompca/smt", name);
		if (name == null) return null;
		
		if (name.equals(CEIL_FUNCTION.getName())) return CEIL_FUNCTION;
//		if (name.equals(CEIL_GUARD_FUNCTION.getName())) return CEIL_GUARD_FUNCTION;
		return null;
	}
	
	public static String getPositiveInfinityInt128() {return BigInteger.valueOf(Long.MAX_VALUE).toString();}
	public static String getNegativeInfinityInt128() {return BigInteger.valueOf(Long.MIN_VALUE).toString();}

	public static String getSimulatedPositiveInfinityInt() {return "MAX_INT";}
	public static String getPlatformPositiveInfinityInt() {return "MAX_MAX_INT";}
	public static String getPlatformNegativeInfinityInt() {return "MIN_INT";}
	
	public static String getPlatformPositiveInfinityReal() {return "MAX_REAL";}
	public static String getPlatformNegativeInfinityReal() {return "MIN_REAL";}
	
	@SuppressWarnings("deprecation")
	public static String getPlatformLibraryFunction(
			SerialFormat format, String library, String id) throws IllegalStateException {
		if (format == null || id == null) return null;
		
		if (library == null) for (String l : Z3_SMT_LIBRARY_FUNCTIONS.key1Set()){
			String f = getPlatformLibraryFunction(format, l, id);
			if (f != null) return f;
		}
		else switch (format) {
		case Z3:		
			break;
		case Z3_SMT:
			Map<Function, String> fs = Z3_SMT_LIBRARY_FUNCTIONS.get(library, id);
			if (fs != null) {
				if (fs.isEmpty()) throwIllegalStateException("not initiated?");
				return fs.values().iterator().next();
			}
		default:
		}
		return null;
	}
	
	public static String getPlatformConditions(SerialFormat format) {
		switch (format) {
		case Z3_SMT:
			return Char.toDefinitionString(SerialFormat.Z3_SMT) + "\n" +
					ompca.vodcg.condition.data.String.toDeclarationString(SerialFormat.Z3_SMT) + "\n" +
					FiniteNumberGuard.toZ3SmtDeclaration();
			
		default:
			return "UNSUPPORTED PLATFORM " + format + "!";
		}
	}
	
	public void resetPlatformDeclaration() {
		// TODO? use elemental declaration injection: List<Runnable>
		Char.resetPlatformDeclaration();
		KEYWORD_POOL.clear();
	}
	

	
	/**
	 * This getter is responsible for traversing the writing history of TV (path).
	 * conds and side-effect are NOT merged during GenCond.
	 * 
	 * @return both parallel and path condition with Z3 top-level functions.
	 */
	public String generateConditionString() {
		if (tv == null) throwNullArgumentException("target variable");
//		if (conds == null) conds = new VOPConditions(this);
		//	iii. parallel conditions ParallelCond
		//	iv. return ParallelCond || PathCond
//		TODO: conds = generatePathConditionsOf(tv, false, "");
		
		int lastIncompletesCount = 0;
		String lastException = "";
		while (true) {
			try {
				conds.add(tv.getConditions(""));
				conds.or(Function.getCOnes());
//				conds.or(BooleanFunction.getAll());
				return conds.toString(SerialFormat.Z3_SMT);
				
			} catch (Exception e) {
//				final PrintStream ps = new PrintStream(System.err);
//				ps.flush();
//				e.printStackTrace(ps);
				final String incompletesException = e.toString() 
						+ Elemental.get(()-> e.getCause().toString(), e_-> "");
				if (lastException.equals(incompletesException)) {
					if (e instanceof IncomparableException || e instanceof ASTException) {
						log(null, "Some exception remains: " + e);
					}
					throwTodoException(e);
				}
				lastException = incompletesException;
			}
				
			// checking completeness of all OV's
			int incompletesCount = 0;
			for (Assignable<?> ovRef : Assignable.getAll()) {
				if (ovRef.enters()) {
					ovRef.leaveTotally();
					log(null, "In-complete generation: " + ovRef);
					incompletesCount++;
				}
			}
			if (lastException.isEmpty()) {
				if (incompletesCount == 0) break;
				if (lastIncompletesCount == incompletesCount) break;	//throwReductionException();
			}
			lastIncompletesCount = incompletesCount;
		}
		
		return null;
	}

	
	
//	private int computeWorkOf(final Assignable ov) {
//		assert ov != null;
//		if (ov.enters(METHOD_COMPUTE_WORK_OF)) return 0;
//		
//		if (Elemental.testsNot(ov.isAssigned())) {
//			final Assignable pov = ov.previousAssigned();
//			return pov == null ? 0 : computeWorkOf(pov);
//		}
//		
//		final SortedSet<Assignable> whSet = getWritingHistoryOfBeforeTP(ov).headSet(ov, true);
//		if (whSet == null || whSet.isEmpty()) checkIncomparable(ov, "No writing history for " + ov);
//		final Assignable[] wh = whSet.toArray(new Assignable[]{});	assert wh != null;
//		final int whSize = wh.length;								assert whSize > 0;
//		int work = 0;
//		
//		for (int whi = whSize - 1, whi_ = -1; whi >= 0; whi--, work++) {
//			final Assignable ovNow = wh[whi];
//			if (ovNow != ov && ovNow.enters(METHOD_COMPUTE_WORK_OF)) continue;
//			try {
//				ovNow.enter(METHOD_COMPUTE_WORK_OF);
//				for (Assignable ovnAsger : ovNow.getAssigners())	// computing side-effects 
//					work += computeWorkOf(ovnAsger);
//				ovNow.leave(METHOD_COMPUTE_WORK_OF);
//				
//			} catch (IllegalStateException e) {
//				ovNow.leave(METHOD_COMPUTE_WORK_OF);
//				if (whi_ == whi) throw e;
//				whi_ = whi;
//				whi = whSize;
//			} catch (Exception e) {
//				throwInvalidityException(e);
//			}
//		}
//		
//		return work;
//	}
	
//	/**
//	 * completes though inconsistent maybe
//	 * 
//	 * @param ov
//	 * @param wh
//	 * @return
//	 */
//	private int completesPathConditionsOf(PathVariable ov, Assignable[] wh) {
//		assert ov != null && wh != null;
//		Assignable[] whCache = COND_PROGRESS_CACHE.getValue2(ov);
//		final int whCacheSize = whCache == null ? 0 : whCache.length;
//		int whi = 0;
//
//		for (; whi < whCacheSize; whi++) 
//			if (!whCache[whi].equals(wh[whi])) return 0;	// dropping inconsistent cache
//		return whi;
//	}
//	
//	private boolean isCompletingGenCondOf(Assignable ovr) {
//		assert ovr != null;
//		return ovr.isCompletingGenCond(METHOD_GENERATE_CONDITIONS_OF);
//	}
	
//	private boolean isBusyGeneratingConditionsOf(Assignable[] ovrs) {
//		assert ovrs != null;
//		for (Assignable ovr : ovrs) if (ovr.enters(METHOD_GENERATE_CONDITIONS_OF);
//	}
	
	@Override
	protected Boolean cacheConstant() {
		return true;
	}

	

	/**<pre>
	 * If OV's global: WES ||= finding WES in main.c and all its sub-function calls 
	 * before the target position TP.
	 * 
	 * ovWrs: <code>SortedSet<IASTName>(wrPosComparator);</code>
	 * 
	 * @param ov - the observed variable, OV
	 * @return a non-null set given non-null <code>ov</code>.
	 */
	public NavigableSet<Assignable<?>> getWritingHistoryOfBeforeTP(Assignable<?> ov) {
		if (ov == null) return null;
		
		try {
		// an OV-separated cache is more efficient than an OV-mixed set
		@SuppressWarnings("unchecked")
		PathVariable ovPv = PathVariable.from((Assignable<PathVariable>) ov);
		NavigableSet<Assignable<?>> ovWrs = WH_CACHE.get(ovPv);
		if (ovWrs != null) return ovWrs;
		
		ovWrs = getLocalWritingHistoryOfBeforeTV(ov);
		if (!testsNonNull(()-> ov.isGlobal())) return setWritingHistoryCacheOf(ovPv, ovWrs); 
		return setWritingHistoryCacheOf(ovPv, getGlobalWritingHistoryOfBeforeTV(ov, ovWrs));
//			return whObserver.observe(ov, ASTUtil.getMainFunctionDefinition(ov), true);
//			return whObserver.observe(ov, ASTUtil.getWritingFunctionDefinition(ov));
		
		} catch (Exception e) {
			return throwTodoException(e);
		}
	}
	
	/**
	 * @param ov
	 * @return a non-null set.
	 */
	private NavigableSet<Assignable<?>> getLocalWritingHistoryOfBeforeTV(Assignable<?> ov) {
		assert ov != null;
		if (tv == null) throwNullArgumentException("target variable"); 
		
		final NavigableSet<Assignable<?>> ovWrs = new TreeSet<Assignable<?>>(tv);
//		SortedSet<LValue> ovWrs = Collections.synchronizedSortedSet(
//				new TreeSet<>(tv));
		
		for (Assignable<?> ovRef : Assignable.fromOf(
				ov.getWritingFunctionDefinition(), ov.getName(), ov.cacheRuntimeAddress(), this)) {
			ovRef.setWorkRemaining();
			if (ovRef == tv || tests(ovRef.writesBefore(tv)))
				ovWrs.add(ovRef);
//			else if (!Elemental.testsNot(ovRef.isAssigned()))	// check when assigned or not sure
//				tv.isIncomparableTo(ovRef, "Incomparable ovRef : " + ovRef);
			ovRef.setWorkRemaining(0, null, "Found local WH of " + ovRef);
		}
		
		return ovWrs;
	}
	
	/**
	 * @param ov
	 * @return writings of the same name as ov, without indirect writings like function calls, etc.
	 */
	private NavigableSet<Assignable<?>> getGlobalWritingHistoryOfBeforeTV(Assignable<?> ov, NavigableSet<Assignable<?>> ovWrs) {
		assert ov != null && tv != null;
		
		if (ovWrs == null) ovWrs = new TreeSet<>(tv);
		IIndex tvIndex = ASTUtil.getIndex(false);
		try {
			tvIndex.acquireReadLock();
			
//			IIndexName[] ovRefs = tvIndex.findReferences(
//					ov.getName().resolveBinding());				// internal NullPointerException!
			for (IIndexBinding ovRef : tvIndex.findBindings(
					ov.getName().toCharArray(), IndexFilter.ALL, new NullProgressMonitor())) {
				IIndexName[] ovRefs = tvIndex.findReferences(ovRef);
				if (ovRefs != null) for (
						int i = 0, ovRefsSize = ovRefs.length; i < ovRefsSize; i++) {
					Assignable<?> ovRefLv = Assignable.from(ovRefs[i], false, this);
					ovRefLv.setWorkRemaining();
					if (ovRefLv != null && !containsLinearly(ovWrs, ovRefLv)) {
						if (ov.equalsVariable(ovRefLv) && tests(ovRefLv.writesBefore(tv))) 
							ovWrs.add(ovRefLv); 
//						else if (!Elemental.testsNot(ovRefLv.isAssigned()))		// check when assigned or not sure
//							tv.isIncomparableTo(ovRefLv, "Incomparable ovRef : " + ovRefLv);
					}
					ovRefLv.setWorkRemaining(0, 
							String.valueOf(i + 1) + "/" + ovRefsSize + "[" + ovRefLv.getShortNameAddress() + "]", 
							"Found global WH");
				}
			}
		} catch (Exception e) {
//			e.printStackTrace();
		} finally {
			tvIndex.releaseReadLock();
		}
		return ovWrs;
	}



	static private NavigableSet<Assignable<?>> setWritingHistoryCacheOf(
			PathVariable ov, NavigableSet<Assignable<?>> ovWrs) {
		WH_CACHE.put(ov, ovWrs);
		return ovWrs;
	}



	public Assignable<?> getTargetVariable() {
		return tv;
	}
	
	/**
	 * The target variable, TV, setter is responsible for preparing project IndexManager.
	 * 
	 * Preparing project IndexManager -> Traversing the initial writing history of TV (path).
	 * 
	 * @param tvPath - the path to target variable
	 */
	public void setTargetVariable(VariablePath tvPath) {
		if (tvPath == null) throwNullArgumentException("TV path");
		
		NavigableSet<Assignable<?>> tvWrs = null;
		final NavigableSet<Assignable<?>> tvRefs = Assignable.fromOf(ASTUtil.getAST(	// Loading C-Index AST
				tvPath.getFilePath(), true), tvPath.getName(), null, this);
		
//		IASTName[] tvRefs = tvAST.getReferences(tvPath.getName().resolveBinding());
//		if (tvRefs != null) for (IASTName tvRef : tvRefs) {
		
//		IIndexName[] tvRefs = tvIndex.findReferences(tvIndex.adaptBinding(tvPath.getName().resolveBinding()));
//		IIndexBinding[] tvBinds = tvIndex.findBindings(
//				tvPath.getName().toCharArray(), false, IndexFilter.ALL, new NullProgressMonitor());
//		if (tvBinds != null) for (IIndexBinding tvBind : tvBinds) {
//			IIndexName[] tvRefs = tvIndex.findReferences(tvBind);
//		}
		final int tpLine = tvPath.getLine();	// target position, TP
		for (Assignable<?> tvRef : tvRefs) {
			if (tvRef.getFileLocation().getStartingLineNumber() == tpLine) tv = tvRef;

			final Boolean tia = tvRef.isAssigned();
			if (tia == null) throwTodoException(tvRef.toString());
//			if (tia == null) tvRef.throwUncertainPlaceholderException();
			if (tia) {
				if (tvWrs == null) tvWrs = new TreeSet<>(tvRef);
//					tvWrs = Collections.synchronizedSortedSet(new TreeSet<>(tv));
				tvWrs.add(tvRef);
			}
		}

		if (tv == null) throwNullArgumentException("target variable");
		try {
		for (Assignable<?> tvRef : tvRefs) {
			final Boolean wbtv = tvRef.writesBefore(tv);
			if (wbtv == null) log("Incomparable " + tvRef.getShortNameAddress() + 
					" and " + tv.getShortNameAddress());
			else if (wbtv) {
				if (tvWrs == null) tvWrs = new TreeSet<>(tvRef);
//				if (tvWrs == null) tvWrs = Collections.synchronizedSortedSet(
//					new TreeSet<>(tvRef));
				tvWrs.add(tvRef);
			} 
		} 
			
//		whObserver = new WritingHistoryObserver(tvWrs);
		setWritingHistoryCacheOf(tv.getPathVariable(), 
				tv.isGlobal() 
				// a global TV needs to search more translation units 
				? getGlobalWritingHistoryOfBeforeTV(tv, tvWrs) 
				// while a single search is sufficient for a local TV
				: tvWrs);

		} catch (Exception e) {
			throwTodoException(e);
		}
	}

	
	
//	public void setGlobal() {
//		final VODCondGen cg = CondGen.get();
//		if (cg != this) throwTodo
//	}

	
	
	static private <T> boolean containsLinearly(Collection<T> objs, T obj) {
		return Arrays.asList(objs).contains(obj);
	}
	
	/* (non-Javadoc)
	 * @see java.util.Comparator#compare(java.lang.Object, java.lang.Object)
	 */
	@Override
	public int compare(IASTForStatement loop1, IASTForStatement loop2) {
		if (loop1 == null) throwNullArgumentException("loop1");
		if (loop2 == null) throwNullArgumentException("loop2");
		return new ASTRuntimeLocationComputer(this).compare(loop1, loop2);
	}

	public SortedSet<IASTForStatement> getLoopHistoryOfBeforeTP(Assignable<?> lv) {
		final SortedSet<Assignable<?>> lvh = getWritingHistoryOfBeforeTP(lv);
		if (lvh == null || lvh.isEmpty()) return Collections.emptySortedSet();
		
		SortedSet<IASTForStatement> lh = LH_CACHE.get(lvh);
		if (lh == null) {
			lh = new TreeSet<>(this);
			for (Assignable<?> plv : lvh) {
				IASTNode lvn = plv.getTopNode();
				while (true) {
					@SuppressWarnings("unchecked")
					IASTForStatement loop = (IASTForStatement) ASTUtil.getAncestorOfAs(
							lvn, new Class[] {IASTForStatement.class}, false);
					if (loop == null) break;
					lh.add(loop);
					lvn = loop;
				}
			}
			LH_CACHE.put(lvh, lh);
		}
		return lh;
	}
	


	/**<pre>
	 * Main function searching strategy: 
	 * 	OV's parent translation unit -> sibling translation units in the parent folder
	 * <br>
	 * 
	 * @param ov - observed variable, OV
	 * @return
	 */
	public IASTFunctionDefinition getMainFunctionDefinitionOf(IASTName ov) {
		// searching OV's parent translation unit 
		// IASTFunctionDefinition extends IASTDeclaration
		for (IASTDeclaration decl : ov.getTranslationUnit().getDeclarations())
			if  (isMainFunction(decl)) return (IASTFunctionDefinition)decl;
		
		// TODO: searching OV's sibling translation units in the parent folder
		
		return null;
	}
	
	public void setMain(IPath mainPath) {
		if (mainPath == null) throwInvalidityException("Main path");
		this.mainPath = mainPath;
	}



	public boolean isInMainTranslationUnit(IASTFunctionDefinition f) {
		return f.getFileLocation().getFileName().equals(mainPath.toOSString());
	}

	public boolean isInMainFunction(IASTNode node) {
		return isMainFunction(ASTUtil.getWritingFunctionDefinitionOf(node));
	}

	public boolean isInFunction(IASTNode node) {
		return ASTUtil.getWritingFunctionDefinitionOf(node) != null;
	}
	
	public boolean isMainFunction(IASTNode node) {
		return node instanceof IASTFunctionDefinition
				? isMainFunction((IASTFunctionDefinition) node)
				: false;
	}
	
	/**
	 * @param f
	 * @return true only if f is the <em>current main being compiled</em> but not any else
	 */
	public boolean isMainFunction(IASTFunctionDefinition f) {
		return ASTUtil.isMainFunction(f) && isInMainTranslationUnit(f);
	}

//	public boolean isMainFunction(IIndexName f) {
//		return f.isDefinition() && f.getSimpleID().equals(ASTUtil.MAIN_FUNCTION_NAME) 
//				&& ASTUtil.getAST(mainPath, true);
//	}

	public boolean isMainFunction(IFunction f) {
		IASTName[] mainDefs = ASTUtil.getAST(mainPath, true).getDefinitionsInAST(f);
		return mainDefs.length > 0 && 
				new String(mainDefs[0].getSimpleID()).equals(ASTUtil.MAIN_FUNCTION_NAME);
	}
	
	
	
	public static boolean isLibraryFunction(String library, String id) {
		if (id == null) throwNullArgumentException("id");
		
		return library == null
				? Z3_SMT_LIBRARY_FUNCTIONS.key2Set().contains(id)
				: Z3_SMT_LIBRARY_FUNCTIONS.get(library, id) != null;
	}

	public static boolean isBounded(PlatformType type) {
		if (type instanceof PointerType) 
			return true;	// limited memory address
		if (type instanceof DataType) switch ((DataType) type) {
		case Bool:
		case Char:
		case Void:
		case Real:	//TODO: ANSI C float128?
		case Int:	return true;
		default:
		}
		return false;
	}

	public static boolean isGlobal(Function f) {
		return f == null || tests(f.isGlobal());
	}



//	/**
//	 * Command line pattern:
//	 * 	java VOPCondGen <var:line@project/folder/file.c> > <smt2_file> 
//	 * @param args
//	 */
//	public static void main(String[] args) {
////		final String argVarPath = args[0];
//		final IPath mainPath = null;	// TODO: args[1].toIPath(...);
//		
//		VOPCondGen condGen = new VOPCondGen(mainPath);
//		condGen.setTargetVariable(new VariablePath(args[0], condGen));
//		System.out.println(condGen.generatePathConditions().toString(SerialFormat.Z3_SMT));
//		System.exit(0);
//	}



//	/**
//	 * TODO: Calling Z3 to check with inherited environment setting.
//	 * 
//	 * @param formulae
//	 * @return The (check-sat) result, including 'timeout', 'unknown', 'unsat' and 'sat' with model in the longest length
//	 * @throws IOException
//	 */
//	static String z3check(String formulae) throws IOException {
//		FileWriter tw = new FileWriter(autoSmtFileName);
//		tw.write(formulae);
//		tw.close();
//
//		InputStream pipe = Runtime.getRuntime().
//				exec(new String[] {"z3",TIMEOUT_ARG_PREFIX + TopDigitCarryInTimeout,"-smt2","--",autoSmtFileName}).getInputStream();
//		// for debug use:
//		//InputStream pipe = Runtime.getRuntime().
//		//		exec(new String[] {"z3","-T:30","-smt2",autoSmtFileName}).getErrorStream();
//		
//		byte[] checkSatBuffer = new byte[1];
//		String checkSat = new String();
//		boolean nlAlready = false;
//		do {	// treating \n\n as Z3 output termination signal
//			try {
//				pipe.read(checkSatBuffer);
//				if (checkSatBuffer[0] == '\n') {if (nlAlready) break; else nlAlready = true;}	// TODO: System.getProperty("line.separator")
//				else nlAlready = false;
//			} catch (IOException e) {break;}
//			checkSat += new String(checkSatBuffer);
//		} while (true);
//		pipe.close(); 
//		return checkSat;
//	}

//	final private Set<String> actions = new HashSet<>();
	
	public <T> T log(String progress, String action) {
		return log(progress, action, (SubMonitor) null);
	}
	
	public <T> T log(String progress, String action, SubMonitor monitor) {
		if (action == null) throwNullArgumentException("action");
//		if (actions.contains(action)) throwTodoException("redundant action");
//		actions.add(action);
		
		if (progress != null && !progress.isBlank()) {
			if (Character.isDigit(progress.charAt(progress.length()-1))) 
				throwTodoException("better provide variable names");
			CacheProgress = progress;
		}
		final int pSize = CacheProgress.length(), pPart = 20;
		final boolean pIsLong = pSize > (2 * pPart + "...".length());
		
		setStart();
		final LocalDateTime now = LocalDateTime.now();
		final String message = ChronoUnit.HOURS.between(start, now) + "h" 
				+ ChronoUnit.MINUTES.between(start, now)%60 + "m)" 
				+ now.format(MONTH_DATE_TIME) + ") "
				+ CacheProgress.substring(0, pIsLong ? pPart : pSize) 
				+ (pIsLong ? "..." + CacheProgress.substring(pSize - pPart) : "") 
				+ " - " + action.replace('\n', '\t');
		java.awt.Toolkit.getDefaultToolkit().beep();
//		getDisplay().beep();
//		System.out.print("\b");	doesn't work on my VM's!
//		System.out.print("\007");	doesn't work on my VM's!
		System.out.println(message);
		if (monitor == null) monitor = rootMonitor;
		if (monitor != null) monitor.subTask(message);
		return null;
	}

	public void setStart() {
		if (start == null) start = LocalDateTime.now();
	}
	
	public void setStart(IProgressMonitor monitor, String task, VariablePath tvPath) {
		reset();
		setStart();
		setTargetVariable(tvPath);
		
		this.rootMonitor = SubMonitor.convert(monitor);
		monitor.beginTask(task, IProgressMonitor.UNKNOWN);
//		monitor.beginTask(task, computeWorkOf(tv));
	}
	
	public void reset() {
		start = null;
		rootMonitor = null;
		resetPlatformDeclaration();
	}
	
	public void done(String progress, String action) {
		log(progress, action, rootMonitor);
		if (rootMonitor != null) rootMonitor.done();
	}
	
	public SubMonitor splitMonitor() {
		if (rootMonitor == null) rootMonitor = SubMonitor.convert(null);
		return rootMonitor.split(1);
	}
	
	public void worked(int work) {
		workRemaining += work;
		if (workRemaining < 0) throwInvalidityException("negative work");
		
		if (rootMonitor == null) rootMonitor = SubMonitor.convert(null);
		rootMonitor.setWorkRemaining(workRemaining);
		rootMonitor.setTaskName(workRemaining + " l-value-times are waiting for processing...");
	}
	
	public void worked(String progress, String action) {
		log(progress, action, rootMonitor);
		if (rootMonitor != null) rootMonitor.worked(1);	// 1 work unit for 1 completed assignable condGen
	}

}