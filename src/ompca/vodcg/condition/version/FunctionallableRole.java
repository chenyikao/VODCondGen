/**
 * 
 */
package ompca.vodcg.condition.version;

/**
 * @author Kao, Chen-yi
 *
 */
public interface FunctionallableRole extends ThreadRoleMatchable {

	public boolean isFunctional();
	
	@Override
	default public boolean isPrivate() {
		return getBasic().isPrivate();
	}

	default public boolean derivesBasic(FunctionallableRole role2) {
		return equalsBasic(role2);
	}
	
	default public boolean equalsBasic(FunctionallableRole role2) {
		return role2 != null 
				&& getBasic().equals(role2.getBasic());
	}
	
//	@Override
//	default public boolean matches(ThreadRoleMatchable role2) {
//		return !role2.isFunctional() && matches(role2.getBasic());
//	}

	public ThreadRole getBasic();
	
	@Override
	default public FunctionallableRole getThreadRole() {
		return this;
	}
	
}