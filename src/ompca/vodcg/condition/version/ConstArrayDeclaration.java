/**
 * 
 */
package ompca.vodcg.condition.version;

import java.util.Arrays;

import ompca.vodcg.Assignable;
import ompca.vodcg.IncomparableException;
import ompca.vodcg.ReenterException;
import ompca.vodcg.UncertainPlaceholderException;
import ompca.vodcg.condition.Expression;
import ompca.vodcg.condition.PathVariable;
import ompca.vodcg.condition.VariablePlaceholder;
import ompca.vodcg.condition.data.Int;

/**
 * Representing a group of {@link ArrayAccessVersion}'s at some declarative array variable placeholder.
 * 
 * @author Kao, Chen-yi
 *
 */
public class ConstArrayDeclaration extends Version<PathVariable> {

	private ConstArrayDeclaration(VersionEnumerable<PathVariable> address)
			throws NoSuchVersionException {
		super(address, ThreadRole.CONST);
	}

	public static Version<? extends PathVariable> from(Assignable<PathVariable> asn) throws NoSuchVersionException {
		if (asn == null) throwNullArgumentException("assignable");
		if (!asn.isDeclarator() || !asn.isArray()) throwNoSuchSubVersionException(asn);

		return new ConstArrayDeclaration(asn);
	}

	
	
//	@Override
//	public Version<PathVariable> cloneRename(String newName) {
//		@SuppressWarnings("unchecked")
//		final Version<PathVariable> nv = (Version<PathVariable>) super.clone();
//		nv.setAssigned(true);	// declaration clone
//		return nv;
//	}

	@SuppressWarnings("unchecked")
	public VariablePlaceholder<PathVariable> getAssigned(int i, Expression rhs) {
		try {
			return (VariablePlaceholder<PathVariable>) VariablePlaceholder.fromNonAST(
					getName() + "[" + i + "]", isGlobal(), true, rhs, getCondGen(),
					addr-> (ArrayAccessVersion<PathVariable>) ArrayAccessVersion.from(
							Arrays.asList(Int.from(i, null)), 
							this, 
							(VersionEnumerable<PathVariable>) addr, 
							ThreadRole.CONST));

		} catch (ReenterException | IncomparableException | UncertainPlaceholderException | NoSuchVersionException e) {
			return throwTodoException(e);
		}
	}

	@Override
	public boolean matches(ThreadRoleMatchable matchable2) {
		if (matchable2 == null) throwNullArgumentException("matchable");
		return matchable2.equals(ThreadRole.CONST)
				? true : super.matches(matchable2);
	}
	
}