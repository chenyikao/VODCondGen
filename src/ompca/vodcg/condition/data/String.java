/**
 * 
 */
package ompca.vodcg.condition.data;

import java.util.ArrayList;
import java.util.EnumMap;
import java.util.HashMap;
import java.util.Map;

import ompca.Mappable;
import ompca.condition.SerialFormat;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.condition.Expression;
import ompca.vodcg.condition.Relation;

/**
 * A string equals an array (concatenation) of {@link Char}'s.
 * 
 * @author Kao, Chen-yi
 *
 */
public class String extends Relation {

	public enum Operator implements Relation.Operator {
		concat;
		
		/* (non-Javadoc)
		 * @see ompca.condition.Relation.Operator#isAssociativeTo(ompca.condition.Relation.Operator)
		 */
		@Override
		public boolean isAssociativeTo(ompca.vodcg.condition.Relation.Operator op) {
			return op.equals(concat);
		}
		@Override
		public boolean isCommutative() {return false;}
		
		@Override
		public <M extends Map<?,?>> EnumMap<? extends Key, M> createPartitionMap() {
			return new EnumMap<>(Operator.class);
		}
		
		@Override
		public <M extends Mappable<?, ?>> EnumMap<? extends Key, M> createPartitionMappable() {
			return new EnumMap<>(Operator.class);
		}

		/* (non-Javadoc)
		 * @see ompca.condition.Relation.Operator#negate()
		 */
		@Override
		public ompca.vodcg.condition.Relation.Operator negate() {
			return null;
		}

		/* (non-Javadoc)
		 * @see java.lang.Enum#toString()
		 */
		@Override
		public java.lang.String toString() {
			return "";
		}

		/* (non-Javadoc)
		 * @see ompca.condition.Relation.Operator#toZ3SmtString(ompca.condition.Relation, boolean, boolean)
		 */
		@Override
		public <H extends Relation> java.lang.String toZ3SmtString(
				H host, boolean printsVariableDeclaration, boolean printsFunctionDefinition) {
			return "";
		}

	}
	
	
	
	private static final Map<java.lang.String, String> STRING_CACHE = 
			new HashMap<>();

//	private List<Char> chars = null;
	private java.lang.String charsString = null;
	
	/**
	 * @param value
	 * @param scopeManager
	 */
	private String(java.lang.String value, VODCondGen scopeManager) {
		super(Operator.concat, new ArrayList<Char>(), scopeManager);
		
		assert (value != null && !value.isEmpty());
		charsString = value;
		for (int i = 0; i < value.length(); i++) 
			add(Char.from(value.charAt(i)));
	}

	public static String from(char[] value, VODCondGen scopeManager) {
		if (value == null || value.length == 0) return null;
		return from(new java.lang.String(value), scopeManager);
	}
	
	public static String from(java.lang.String value, VODCondGen scopeManager) {
		if (value == null || value.length() == 0) return null;
		
		String str = STRING_CACHE.get(value);
		if (str == null) 
			STRING_CACHE.put(value, str = new String(value, scopeManager));
		return str;
	}

	
	
	/* (non-Javadoc)
	 * @see ompca.condition.Expression#getType()
	 */
	@Override
	public PlatformType getType() {
		return DataType.Array;
	}
	
	
	
	/* (non-Javadoc)
	 * @see ompca.condition.Expression#negate()
	 */
	@Override
	public Expression negate() {
		return null;
	}
	
	
	
	public static boolean isUsed() {
		return true;
//		return !STRING_CACHE.isEmpty();
	}


	
	/**
	 * A string is globally constant.
	 * 
	 * @see ompca.condition.Relation#isGlobal()
	 */
	@Override
	protected Boolean cacheGlobal() {
		return true;
	}
	
	/**
	 * A string is globally constant.
	 * 
	 * @see ompca.condition.Expression#isConstant()
	 */
	protected Boolean cacheConstant() {
		return true;
	}

	protected Expression toConstantIf() {
		return this;
	}
	
	
	
	/**
	 * @param format
	 * @return
	 */
	public static java.lang.String toDeclarationString(SerialFormat format) {
		if (isUsed()) switch (format) {
		case Z3_SMT:	// to Z3 scalar type
//			java.lang.String def = "(declare-datatypes () ((" + toZ3SmtType();
//			for (String str : STRING_CACHE.values()) 
//				def += (" " + str.toZ3SmtString(false, false));
//			return def + ")))";
			return "(declare-sort Char)\n"
					+ "(define-sort Str () (Array Int Char))";
		case Z3:	// TODO
		default:
		}
		return "";
	}


	
	@Override
	protected java.lang.String toNonEmptyString(boolean usesParenAlready) {
		return charsString;
	}
	
	/* (non-Javadoc)
	 * @see ompca.condition.ConditionElement#toZ3SmtString()
	 */
	@Override
	public java.lang.String toZ3SmtString(
			boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs) {
		// disambiguating with Char
		return disambiguateZ3SmtString(charsString, null);
		
//		java.lang.String str = "";
//		for (Char c : chars) str += c.toZ3SmtString(
//				printsVariableDeclaration, printsFunctionDefinition);
	}

	public static java.lang.String toZ3SmtType() {
		return "Str";
	}
	
	@Override
	public java.lang.String disambiguateZ3SmtString(
			java.lang.String originalTerm, java.lang.String disambiguousTerm) {
		originalTerm = originalTerm.replaceAll("[:\\.\\s\\(\\)\\\\]", "_");
		if (Character.isDigit(originalTerm.charAt(0))) originalTerm = "_" + originalTerm;
		if (originalTerm.length() == 1) originalTerm += ("_" + toZ3SmtType()); 
		
		if (disambiguousTerm == null) disambiguousTerm = "_" + originalTerm;
		return super.disambiguateZ3SmtString(originalTerm, disambiguousTerm);
	}
	
}