package ompca.vodcg.condition.version;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.function.Supplier;

import ompca.Elemental;
import ompca.vodcg.DebugElement;
import ompca.vodcg.SystemElement;
import ompca.vodcg.condition.ArithmeticExpression;
import ompca.vodcg.condition.Expression;

/**
 * @author Kao, Chen-yi
 *
 */
public interface ThreadRoleMatchable {

	public Boolean isConstant();
	
	/**
	 * @return 
	 * @throws unknown exception even if this is either private or shared.
	 * 	isPrivate - thread-private non-array locals are not functional;
	 * 	isShared - shared non-arrays or arrays without loops/pragmas are not functional.
	 */
	default public boolean isFunctional() {
		if (SystemElement.tests(isConstant())) return false;
		return getNonNullThis(()-> getThreadRole().isFunctional());
	}
	
	default public boolean isPrivate() {
		return getNonNullThis(()-> getThreadRole()).isPrivate();
	}
	
	default public boolean isShared() {
		return !isPrivate();
	}
	
	default public <T> T getNonNullThis(Supplier<T> sup) {
		final T result = Elemental.getNonNull(sup);
		return result == this
				? throwUnsupportedRoleException()
				: result;
	}

	default public FunctionallableRole getThreadRole() {
		return Elemental.tests(isConstant())
				? ThreadRole.CONST
				: ThreadRole.MASTER;
//				: throwUnsupportedRoleException();
	}
	
	/**
	 * @param exps - including possibly null expression elements.
	 * @return
	 */
	static public FunctionallableRole getThreadRole(Collection<? extends Expression> exps) {
		if (exps == null) return null;
		
		FunctionallableRole role = null;
		for (Expression e : exps) {
			if (e == null) continue;
			final FunctionallableRole eRole = 
					e.guard(()-> e.getThreadRole(), ()-> ThreadRole.MASTER);
			if (role == null || role.derives(eRole)) role = eRole;
		}
		return role;
	}
	
	/**
	 * @param exps - including possibly null expression arguments.
	 * @return
	 */
	static public FunctionallableRole getThreadRole(Expression... exps) {
		if (exps == null) return null;
		return getThreadRole(Arrays.asList(exps));
	}
	
	@SuppressWarnings("deprecation")
	static public FunctionallableRole getThreadRole(ArithmeticExpression... exps) {
		if (exps == null) return null;
		final Collection<Expression> es = new ArrayList<>();
		for (ArithmeticExpression e : exps) {
			if (e == null) continue;
			if (e instanceof Expression) es.add((Expression) e);
			else DebugElement.throwTodoException("unsuported arithmetic exception");
		}
		return getThreadRole(es);
	}
	

	
	/**
	 * @param exps - including possibly null expression arguments.
	 * @return
	 */
	default public ThreadRoleMatchable derive(Expression... exps) {
		return derive(null, exps);
	}
	
	default public ThreadRoleMatchable derive(ThreadRoleMatchable matchable2, Expression... exps) {
		final FunctionallableRole eRole = getThreadRole(exps);
		final Boolean dm2 = matchable2 == null ? null : derives(matchable2),
				der = eRole == null ? null : derives(eRole);
		if (dm2 == null) {
			if (der == null) return this;
			if (der) return eRole;
		} else if (dm2) {
			if (der == null) return matchable2;
			if (der) {
				if (matchable2.derives(eRole)) return eRole;
				return matchable2;
			}
		}
		return SystemElement.throwTodoException("inderivable roles");
	}
	
	/**
	 * @param matchable2
	 * @return true for every constants and race-version-derivable's.
	 * 	Otherwise return match-based derive-ness.
	 */
	default public boolean derives(ThreadRoleMatchable matchable2) {
		if (SystemElement.tests(isConstant()) 
				|| matchable2 instanceof RaceVersion) return true;
		return matchable2 instanceof Version
				? matches(((Version<?>) matchable2).getThreadRole())
				: matches(matchable2);
	}
	
	default public boolean matches(ThreadRoleMatchable matchable2) {
		return equals(matchable2);
	}

	/**
	 * Override-able instance method for sub-classing.
	 * 
	 * @param <T>
	 * @return
	 */
	default public <T> T throwUnsupportedRoleException() {
		return SystemElement.throwTodoException("unsupported role type");
	}
	
}