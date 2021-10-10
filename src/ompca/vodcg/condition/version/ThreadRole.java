package ompca.vodcg.condition.version;

import java.util.Arrays;
import java.util.List;

import ompca.vodcg.FunctionalAssignable;
import ompca.vodcg.SystemElement;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.PathVariable;
import ompca.vodcg.condition.Variable;

public enum ThreadRole implements FunctionallableRole {
	MASTER, NON_MASTER, CONST,
	THREAD1, THREAD2, 
	
	/**
	 * For multi-threading, not single-threading functions, which means
	 * private functional {@link PathVariable}'s or thread ID {@link Variable}'s (function indices/arguments).
	 */
	FUNCTION;
	
//	final static private ExtendedRole THREAD1_EXTENDED 		= new ExtendedRole(THREAD1);
//	final static private ExtendedRole THREAD2_EXTENDED 		= new ExtendedRole(THREAD2);
//	final static private ExtendedRole NON_MASTER_EXTENDED 	= new ExtendedRole(NON_MASTER);
//	final static private ExtendedRole MASTER_EXTENDED 		= new ExtendedRole(MASTER);

	@Override
	public ThreadRole getBasic() {return this;}

	@Override
	public Boolean isConstant() {
		return this == CONST;
	}
	
	@Override
	public boolean isFunctional() {
		return this == FUNCTION;
	}
	
	@Override
	public boolean isPrivate() {
		switch (this) {
		case THREAD1:
		case THREAD2:		return true;
		case FUNCTION:
		case NON_MASTER:
		case MASTER:
		case CONST:			return false;
		default:			return throwUnsupportedRoleException();
		}
	}
	
	@Override
	public boolean derives(ThreadRoleMatchable matchable2) {
		return matchable2 instanceof FunctionallableRole
				? derives((FunctionallableRole) matchable2)
				: FunctionallableRole.super.derives(matchable2);
	}
	
	private boolean derives(FunctionallableRole matchable2) {
		assert matchable2 != null;
		switch (this) {
		case CONST:		
			return !matchable2.isPrivate();
			
		case MASTER:	
		case NON_MASTER:
			return !matchable2.getBasic().equals(CONST);
			
		case FUNCTION:	
			final ThreadRole tr2 = matchable2.getBasic();
			return tr2.equals(FUNCTION) || tr2.equals(THREAD1) || tr2.equals(THREAD2);
			
		case THREAD1:	
		case THREAD2:	
			return FunctionallableRole.super.derives(matchable2);
			
		default:		
		}
		return throwUnsupportedRoleException();
	}
	
//	@Override
//	public boolean matches(ThreadRoleMatchable role2) {
//		return derives(role2);
////		return role2 instanceof FunctionallableRole
////				? matches((FunctionallableRole) role2)
////				: FunctionallableRole.super.matches(role2);
//	}

//	private boolean matches(FunctionallableRole role2) {
//		assert role2 != null;
//		switch (role2.getBasic()) {
//		case FUNCTION:
//		case NON_MASTER:
//		case THREAD1:
//		case THREAD2:	return true;
//		case CONST:
//		case MASTER:
//		default:
//		}
//		return FunctionallableRole.super.matches(role2);
//	}
	
//	public ExtendedRole extend() {
//		switch (this) {
//		case MASTER:	return MASTER_EXTENDED;
//		case NON_MASTER:return NON_MASTER_EXTENDED;
//		case THREAD1:	return THREAD1_EXTENDED;
//		case THREAD2:	return THREAD2_EXTENDED;
//		default:		break;
//		}
//		DebugElement.throwInvalidityException("no extended role");
//		return null;
//	}
	
	public ExtendedRole enumerate(String enumeration) {
		return extend(enumeration);
	}
	
	public ExtendedRole extend(String enumeration) {
		if (enumeration == null || enumeration.isBlank()) SystemElement.throwNullArgumentException("enumeration");
		
		switch (this) {
		case FUNCTION:										// multi-threading
		case THREAD1:										// private single-threading
		case THREAD2:	return new ExtendedRole(this, enumeration);// private single-threading
		
		case MASTER:	
		case NON_MASTER:
		default:		break;
		}
		return SystemElement.throwInvalidityException("using enumeration version instead");
	}
	
	public ExtendedRole extend(FunctionalAssignable arg) {
		if (arg == null) SystemElement.throwNullArgumentException("functional assignable");
		
		switch (this) {
		case FUNCTION:										// multi-threading
		case THREAD1:										// private single-threading
		case THREAD2:	return new ExtendedRole(this, arg);// private single-threading
		
		case MASTER:	
		case NON_MASTER:
		default:		break;
		}
		return SystemElement.throwInvalidityException("unsupported role extension");
	}
	
	public ExtendedRole extend(List<ArithmeticExpression> args) {
		if (args == null || args.isEmpty()) 
			SystemElement.throwTodoException("constant function w/o arguments is NOT allowed");
		
		SW: switch (this) {
		case MASTER:	
			for (ArithmeticExpression arg : args) 
				if (!SystemElement.tests(arg.isConstant())) break SW;	
		case FUNCTION:										// multi-threading
		case THREAD1:										// private single-threading
		case THREAD2:	return new ExtendedRole(this, args);// private single-threading
		
		case NON_MASTER:
		default:		break;
		}
		return SystemElement.throwInvalidityException("unsupported role extension");
	}
	

	
	public static class ExtendedRole implements FunctionallableRole, ArgumentMatchable {
		
		private ThreadRole basicRole = null;
		private List<ArithmeticExpression> args = null;
		private FunctionalAssignable selfAsn = null;
		private String enumeration = null;
		
		private ExtendedRole(ThreadRole basicRole) {
			if (basicRole == null) SystemElement.throwNullArgumentException("basic role");
			
			this.basicRole = basicRole;
		}
		
		private ExtendedRole(ThreadRole basicRole, String enumeration) {
			this(basicRole);
			this.enumeration = enumeration;
		}
		
		private ExtendedRole(ThreadRole basicRole, FunctionalAssignable arg) {
			this(basicRole);
			setArgument(arg);
		}
		
		private ExtendedRole(ThreadRole basicRole, List<ArithmeticExpression> args) {
			this(basicRole);
			setArguments(args);
		}
		
		@Override
		public boolean equals(Object obj) {
			if (obj instanceof ExtendedRole) {
				ExtendedRole role2 = (ExtendedRole) obj;
				return basicRole == role2.basicRole 
						&& args == role2.args 
						&& enumeration == role2.enumeration;
			}
			else if (obj instanceof ThreadRole) 
				return basicRole == (ThreadRole) obj;
			return false;
		}
		
		@Override
		public int hashCode() {
			final int prime = 31;
			return ((basicRole.hashCode() * prime
					+ (args == null ? 0 : args.hashCode())) * prime) 
					+ (enumeration == null ? 0 : enumeration.hashCode());
		}

		
		
		public boolean hasArguments() {
			return selfAsn != null
					|| (args != null && !args.isEmpty());
		}
		
		public boolean hasEnumeration() {
			return enumeration != null && !enumeration.isBlank();
		}
		
		@Override
		public Boolean isConstant() {
			return false;
		}
		
		@Override
		public boolean isFunctional() {
			return basicRole == FUNCTION || hasArguments();
		}
		
//		@Override
//		public boolean isPrivate() {
//			return FunctionallableRole.super.isPrivate() || hasArguments();
//		}

		@Override
		public boolean derives(ThreadRoleMatchable role2) {
			// equivalence-based derivation
			if (FunctionallableRole.super.derives(role2)) return true;
			
			assert !equals(role2);
			return basicRole == FUNCTION && basicRole.derives(role2);
		}
		
		@Override
		public boolean derivesBasic(FunctionallableRole role2) {
			if (FunctionallableRole.super.derivesBasic(role2)) {
				if (role2 instanceof ExtendedRole) {
					final ExtendedRole er2 = (ExtendedRole) role2;
					if (hasEnumeration()) return enumeration.equals(er2.enumeration);
					if (hasArguments()) {
						final List<ArithmeticExpression> args2 = er2.getArguments();
						for (ArithmeticExpression arg : getArguments()) 
							for (ArithmeticExpression arg2 : args2) 
								if (arg.contains(arg2)) return true;
						return false;
					}
					return true;
				} 
				// else role2 instanceof ThreadRole, ...
			}
			return false;
		}

		@Override
		public ThreadRole getBasic() {
			return basicRole;
		}
		
		public List<ArithmeticExpression> getArguments() {
			// delayed self argument getting to avoid matchArgumentsTo(...) - cloneReversion(...) cycle
			return selfAsn != null
					? Arrays.asList(selfAsn.getPathVariablePlaceholder().cloneIfChangeRole(this))
					: args;
		}
		
		private void setArgument(FunctionalAssignable arg) {
			assert arg != null;
			selfAsn = arg;
//			setArguments(Arrays.asList(selfAsn.getPathVariablePlaceholder()));
		}
		
		public void setArguments(List<ArithmeticExpression> args) {
			this.args = matchArgumentsTo(args, this);
		}
		
		public String toEnumeration() {
			return basicRole.toString() 
					+ (enumeration == null ? "" : "_" + enumeration);
		}
		
		@Override
		public String toString() {
			final List<ArithmeticExpression> args = getArguments();
			return toEnumeration()
					+ (args == null ? "[]" : args);
		}
	}
	
}