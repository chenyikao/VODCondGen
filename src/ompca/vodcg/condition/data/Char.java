package ompca.vodcg.condition.data;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import ompca.condition.SerialFormat;
import ompca.vodcg.SystemElement;
import ompca.vodcg.condition.Expression;
import ompca.vodcg.condition.Function;

/**
 * A character is always globally constant.
 * 
 * @author Kao, Chen-yi
 *
 */
public class Char extends Expression {

	// must be initialized first! (as in the source code order)
	private static final Map<Character, Char> CHAR_CACHE = new HashMap<>();
	private static boolean isDefined = false;
	
	private char value;

	
	
	/**
	 * Always global.
	 * 
	 * @param value
	 * @param scopeManager 
	 */
	private Char(char value) {
		super(null, null);
		this.value = value;
	}
	
	public static Char from(char value) {
		Char c = CHAR_CACHE.get(value);	// cached Int
		if (c == null) CHAR_CACHE.put(value, c = new Char(value));
		return c;
	}
	
	public static Char from(char[] value) {
		if (value == null) return null;
		// TODO: using java.util.regex.Pattern parsing C/C++ char constant
		if (value.length == 3 && value[0] == '\'' && value[2] == '\'') 
			return from(value[1]);
		return null;
	}
	
	
	
	/**
	 * @return
	 */
	public static boolean isUsed() {
		return !CHAR_CACHE.isEmpty();
	}
	
	/**
	 * @return
	 */
	public static boolean isUsed(java.lang.Character symbol) {
		return CHAR_CACHE.containsKey(symbol);
	}
	
	/* (non-Javadoc)
	 * @see ompca.vodcg.condition.ConditionElement#isEmpty()
	 */
	@Override
	public boolean isEmpty() {
		return false;
	}
	
	@Override
	protected Boolean cacheGlobal() {
		return true;
	}

	@Override
	protected Boolean cacheConstant() {
		return true;
	}
	
	@SuppressWarnings("unchecked")
	@Override
	protected Char toConstantIf() {
		return this;
	}



//	@Override
//	public java.lang.String getIDSuffix(SerialFormat format) {
//		return "";
//	}

//	@Override
//	public ThreadRole getThreadRole() {
//		return ThreadRole.CONST;
//	}
	
	/* (non-Javadoc)
	 * @see ompca.vodcg.condition.Expression#getType()
	 */
	@Override
	public DataType getType() {
		return DataType.Char;
	}

	@Override
	protected Set<ArithmeticGuard> cacheArithmeticGuards() {
		return null;
	}
	
	@Override
	protected Set<Function> cacheDirectFunctionReferences() {
		return null;
	}
	
	/* (non-Javadoc)
	 * @see ompca.vodcg.condition.ConditionElement#getVariableReferences()
	 */
	@Override
	protected <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType) {
		return null;
	}
	
	@Override
	protected void cacheDirectSideEffect() {
	}
	
	@Override
	public boolean suitsSideEffect() {
		return false;
	}
	

	
	/* (non-Javadoc)
	 * @see ompca.vodcg.condition.Expression#negate()
	 */
	@Override
	public Expression negate() {
		if (Character.isLowerCase(value)) 
			return from(Character.toUpperCase(value));
		if (Character.isUpperCase(value)) 
			return from(Character.toLowerCase(value));
		return this;
	}
	


	/* (non-Javadoc)
	 * @see ompca.vodcg.condition.Expression#containsArithmetic()
	 */
	@Override
	public boolean containsArithmetic() {
		return false;
	}
	
	protected boolean equalsToCache(SystemElement e2) {
		return value == ((Char) e2).value;
	}
	
	protected List<Integer> hashCodeVars() {
		return Arrays.asList(((Character) value).hashCode());
	}
	
	
	
	/**
	 * 
	 */
	public static void resetPlatformDeclaration() {
		isDefined = false;
	}

	/**
	 * @param format
	 * @return
	 */
	public static java.lang.String toDefinitionString(SerialFormat format) {
		if (!isDefined) {
			switch (format) {
			case Z3_SMT:	// to Z3 scalar type
				if (isUsed()) {
					java.lang.String def = "(declare-datatypes () ((Char";
					for (Char c : CHAR_CACHE.values()) 
						def += (" " + c.toZ3SmtString(false, false, false));
					return def + ")))";
				}
//				else Debug.throwInvalidityException("no Chars used yet");
			case Z3:	// TODO
			default:
			} 
			isDefined = true;
		}
		return "";
	}

	public static java.lang.String toTypeString(SerialFormat format) {
		switch (format) {
		case Z3_SMT:
			return "Char";
		case Z3:	// TODO
		default:
			return "";
		}
	}
	
	@Override
	protected java.lang.String toNonEmptyString(boolean usesParenAlready) {
		return Character.toString(value);
	}
	


	/* (non-Javadoc)
	 * @see ompca.vodcg.condition.ConditionElement#toZ3SmtString()
	 */
	@Override
	public java.lang.String toZ3SmtString(boolean printsVariableDeclaration, 
			boolean printsFunctionDefinition, boolean isLhs) {
		// A character has top precedence if ambiguity happened
		return disambiguateZ3SmtString(toNonEmptyString(false), null);
	}

	@Override
	public java.lang.String disambiguateZ3SmtString(
			java.lang.String originalTerm, java.lang.String disambiguousTerm) {
		if (originalTerm.equals(".")) return "DOT";
		if (originalTerm.equals("/")) return "SLASH";;
		if (originalTerm.equals("\\")) return "BACKSLASH";;
		if (originalTerm.equals("(")) return "LEFTPAREN";;
		if (originalTerm.equals(")")) return "RIGHTPAREN";;
		if (originalTerm.equals(":")) return "COLON";;
		if (originalTerm.equals("=")) return "EQ";;
		if (originalTerm.equals("-")) return "MINUS";;
//		if (Character.isDigit(value)) return "_" + value;
		if (Character.isDigit(originalTerm.charAt(0))) return "_" + originalTerm;
		return originalTerm;
	}

}