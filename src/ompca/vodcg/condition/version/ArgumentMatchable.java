package ompca.vodcg.condition.version;

import java.util.ArrayList;
import java.util.List;

import ompca.vodcg.SystemElement;

/**
 * @author Kao, Chen-yi
 *
 */
public interface ArgumentMatchable extends ThreadRoleMatchable {

	default public ArgumentMatchable matchTo(final ThreadRoleMatchable newRole) {
		return SystemElement.throwTodoException("unsupported operation");
	}
	
	@SuppressWarnings("unchecked")
	default public <T> List<T> matchArgumentsTo(
			final List<T> args, final ThreadRoleMatchable newRole) {
		final ArrayList<T> margs = new ArrayList<>();
		if (args != null) for (T arg : args) {
			if (arg instanceof ArgumentMatchable) 
				margs.add((T) ((ArgumentMatchable) arg).matchTo(newRole));
			else 
				SystemElement.throwTodoException("unsupported argument type");
		}
		return margs;
	}
	
//	default public ArgumentMatchable matchArgumentTo(
//			final ArgumentMatchable arg, final ThreadRoleMatchable newRole) {
//		if (arg == null) return SystemElement.throwNullArgumentException("argument");
//		return arg.matchTo(newRole);
//	}
	
//	default public void matchArgumentTo(
//			final ConditionalExpression argce, final ThreadRoleMatchable newRole) {
//		if (argce == null) return;
//		matchArgumentTo(argce.getCondition(), newRole);
//		matchArgumentTo(argce.getTrueExpression(), newRole);
//		matchArgumentTo(argce.getFalseExpression(), newRole);
//	}
	
//	default public void matchArgumentTo(
//			final FunctionCall<?> argfc, final ThreadRoleMatchable newRole) {
//		if (argfc == null || newRole == null) return;
//		if (!newRole.isPrivate()) 
//			DebugElement.throwInvalidityException("inconsistent argument role");
//	}
	
//	default public void matchArgumentTo(
//			final Version<?> argv, final ThreadRoleMatchable newRole) {
//		if (argv == null) return;
//		if (!argv.getThreadRole().matches(newRole)) 
//			DebugElement.throwInvalidityException("inconsistent argument role");
//	}
	
//	default public void matchArgumentTo(
//			final VariablePlaceholder<?> argp, final ThreadRoleMatchable newRole) {
//		if (argp == null) DebugElement.throwNullArgumentException("path variable placeholder");
//
//		if (!argp.peekVersions().isEmpty()) try {
//			// a placeholder guards roles by getVersion(role)
//			if (argp.getVersion(newRole) == null) {
//
//				// argp.isPrivate() && argp.getVersion(newRole) == null => newRole == THREAD1 || THREAD2
//				if (newRole.isPrivate() && argp.isPrivate()) return;
//				
//				DebugElement.throwInvalidityException("unmatchable argument role");
//			}
//			
////				if (argp.matches(newRole)) return;
////			if (argv.matches(newRole)) {
//////				matchArgumentTo(argv, newRole);
////				argp.reversion((Version<? extends PathVariable>) argv.cloneIfChangeRole(newRole));
////			}
//			
//		} catch (UncertainPlaceholderException | ReenterException e) {
//			return;	// for non-initialized placeholder's
//		} catch (Exception e) {
//			DebugElement.throwUnhandledException(e);
//		} 
//	}
	
}