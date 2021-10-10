/**
 * 
 */
package ompca.vodcg.parallel;

/**
 * @author Kao, Chen-yi
 *
 */
public final class OmpUtil {

	public enum Schedule {STATIC, DYNAMIC, GUIDED, RUNTIME, AUTO;

		/**
		 * @param schedule
		 * @return
		 */
		public static Schedule from(String schedule) {
			if (schedule.equals("static")) 	return STATIC;
			if (schedule.equals("dynamic")) return DYNAMIC;
			if (schedule.equals("guided")) 	return GUIDED;
			if (schedule.equals("runtime")) return RUNTIME;
			if (schedule.equals("auto")) 	return AUTO;
			return null;
		}
	}
	
	
	
	public static String patternAny() {				return "(.|" + patternLineBreak() + ")";}
	public static String patternLineBreak() {		return "(\\\\|\\n|\\r\\n|\\r|\\R)";}
	public static String patternLeftParenthesis() {	return "\\s*\\(\\s*";}
	public static String patternRightParenthesis() {return "\\s*\\)\\s*";}
	public static String patternColon() {			return "\\s*:\\s*";}
	public static String patternComma() {			return "\\s*,\\s*";}
	public static String patternVerticalLine() {	return "\\s*|\\s*";}
	
	public static String pattern(final String pattern, String groupName) {
//		boolean hasGroupName = groupName != null;
		return groupName == null || groupName.isEmpty() 
				? pattern : ("(?<" + groupName + ">" + pattern + ")");
	}
	
	public static String patternShared(String groupName) {
		return pattern("shared", groupName);
	}
	
	public static String patternNone(String groupName) {
		return pattern("none", groupName);
	}
	
	public static String patternOrdered(String groupName) {
		return pattern("ordered", groupName);
	}
	
	public static String patternNoWait(String groupName) {
		return pattern("nowait", groupName);
	}
	
	/**<pre><q>Valid Operators and Initialization Values
	 * Operation 			Fortran 	C/C++ 	Initialization
	 * Addition 			+			+ 		0
	 * Multiplication 		*			* 		1
	 * Subtraction 			-			- 		0
	 * Logical AND 			.and. 		&& 		0
	 * Logical OR 			.or. 		|| 		.false. / 0
	 * AND bitwise 			iand 		& 		all bits on / 1
	 * OR bitwise 			ior 		| 		0
	 * Exclusive OR bitwise ieor 		^ 		0
	 * Equivalent 			.eqv. 				.true.
	 * Not Equivalent 		.neqv. 				.false.
	 * Maximum 				max 		max 	Most negative #
	 * Minimum 				min 		min 	Largest positive #</q>
	 * 
	 * @param groupName
	 * @param listGroupName
	 * @param firstListItemGroupName
	 * @param listItemGroupName
	 * @return
	 * @see https://computing.llnl.gov/tutorials/openMP/#REDUCTION
	 */
	public static String patternOperator(String groupName) {
		return pattern("(\\+|\\*|-|&&|\\|\\||&|\\||\\^|max|min)", groupName); 
	}
	
	public static String patternType(String groupName) {
		return pattern("\\w+", groupName);
	}
	
	public static String patternChunk(String groupName) {
		return pattern("\\d+", groupName);
	}
	
	public static String patternListItem(String groupName) {
		return pattern("\\w+", groupName);
	}
	
	public static String patternList(
			String groupName, String firstListItemGroupName, String listItemGroupName) {
		return pattern(patternListItem(firstListItemGroupName) 
						+ "(" + patternComma() + patternListItem(listItemGroupName) + ")*", groupName);
	}
	
	public static String patternParenthesizedList(
			String groupName, String firstListItemGroupName, String listItemGroupName) {
		return patternLeftParenthesis() 
				+ patternList(groupName, firstListItemGroupName, listItemGroupName) 
				+ patternRightParenthesis();
	}
	
	public static String patternScalarExpression(String groupName) {
		return "";	// TODO
	}
	
	public static String patternIntegerExpression(String groupName) {
		return "";	// TODO
	}
	
	public static String patternIf(String groupName, String scalarExpressionGroupName) {
		return pattern("if" + patternLeftParenthesis() 
				+ patternScalarExpression(scalarExpressionGroupName), groupName) 
				+ patternRightParenthesis();
	}
	
	public static String patternSchedule(
			String groupName, String typeGroupName, String chunkGroupName) {
		return pattern("schedule" + patternLeftParenthesis() 
				+ patternType(typeGroupName) + "(" + patternComma() 
				+ patternChunk(chunkGroupName) + ")?", groupName) 
				+ patternRightParenthesis();
	}
	
	public static String patternPrivate(String groupName, 
			String listGroupName, String firstListItemGroupName, String listItemGroupName) {
		return pattern("private" 
			+ patternParenthesizedList(listGroupName, firstListItemGroupName, listItemGroupName), 
			groupName);
	}
	
	public static String patternFirstPrivate(String groupName, 
			String listGroupName, String firstListItemGroupName, String listItemGroupName) {
		return pattern("firstprivate" 
			+ patternParenthesizedList(listGroupName, firstListItemGroupName, listItemGroupName), 
			groupName);
	}
	
	public static String patternLastPrivate(String groupName, 
			String listGroupName, String firstListItemGroupName, String listItemGroupName) {
		return pattern("lastprivate" 
			+ patternParenthesizedList(listGroupName, firstListItemGroupName, listItemGroupName), 
			groupName);
	}
	
	public static String patternShared(String groupName, 
			String listGroupName, String firstListItemGroupName, String listItemGroupName) {
		return pattern("shared" 
			+ patternParenthesizedList(listGroupName, firstListItemGroupName, listItemGroupName), 
			groupName);
	}
	
	public static String patternDefault(
			String groupName, String sharedGroupName, String noneGroupName) {
		return pattern("default" + patternLeftParenthesis() 
				+ patternShared(sharedGroupName) + patternVerticalLine() 
				+ patternNone(noneGroupName), groupName) 
				+ patternRightParenthesis();
	}
	
	public static String patternReduction(String groupName, String operatorGroupName, 
			String listGroupName, String firstListItemGroupName, String listItemGroupName) {
		return pattern("reduction" + patternLeftParenthesis() 
				+ patternOperator(operatorGroupName) + patternColon() 
				+ patternList(listGroupName, firstListItemGroupName, listItemGroupName) 
				+ patternRightParenthesis(), 
				groupName);
	}
	
	public static String patternCopyIn(String groupName, 
			String listGroupName, String firstListItemGroupName, String listItemGroupName) {
		return pattern("copyin" 
			+ patternParenthesizedList(listGroupName, firstListItemGroupName, listItemGroupName), 
			groupName);
	}
	
	public static String patternNumThreads(String groupName, String integerExpressionGroupName) {
		return pattern("num_threads" + patternLeftParenthesis() 
				+ patternIntegerExpression(integerExpressionGroupName), groupName) 
				+ patternRightParenthesis();
	}
	
	public static String patternCollapse(String groupName, String nGroupName) {
		return pattern("collapse" + patternLeftParenthesis() + pattern("\\d+", nGroupName), groupName) 
				+ patternRightParenthesis();
	}
	

	
	public static String trimPragma(String pragma) {
		return pragma == null 
				? null 
				: pragma.replaceAll(patternLineBreak(), "").trim();
	}
	
}