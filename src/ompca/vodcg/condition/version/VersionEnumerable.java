/**
 * 
 */
package ompca.vodcg.condition.version;

import java.util.Collections;
import java.util.List;
import java.util.NavigableSet;
import java.util.TreeSet;

import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

import ompca.DebugElement;
import ompca.Elemental;
import ompca.vodcg.AssignableElement;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.ASTAddressable;
import ompca.vodcg.condition.Referenceable;
import ompca.vodcg.condition.data.PlatformType;
import ompca.vodcg.parallel.ThreadPrivatizable;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public interface VersionEnumerable<Subject extends Referenceable> 
extends ASTAddressable, AssignableElement, ThreadPrivatizable {

//	Set<Version<Variable>> getDirectVariableReferences();
	
	public Boolean isGlobal();
//	public Boolean isDirectlyFunctional();
	
	default public boolean isDeclarator() {
		return !isInAST()
				? DebugElement.throwInvalidityException("non-AST")
				: DebugElement.throwTodoException("unsupported declarator");
	}
	
	default public boolean isParameter() {
		return DebugElement.throwTodoException("unsupported parameter");
	}
	
	default public boolean isLoopIterator() {
		return isLoopIteratingIterator() || isLoopInitializedIterator();
	}
	
	default public boolean isLoopIteratingIterator() {
		return !isInAST()
				? DebugElement.throwInvalidityException("non-AST")
				: DebugElement.throwTodoException("unsupported loop iterator");
	}
	
	default public boolean isLoopInitializedIterator() {
		return !isInAST()
				? DebugElement.throwInvalidityException("non-AST")
				: DebugElement.throwTodoException("unsupported loop iterator");
	}
	
//	default public boolean testsAssigned() {
//		if (this instanceof Assignable) return Elemental.tests(((Assignable) this).isAssigned());
//		if (this instanceof AssignableExpression) return Elemental.tests(((AssignableExpression) this).isAssigned());
//		return DebugElement.throwTodoException("unsupported assignable");
//	}
	

	
	/**
	 * @return non-null
	 */
	@SuppressWarnings("unchecked")
	default public <T extends VersionEnumerable<Subject>> T previousOrUnambiguousAssigned() {
		if (Elemental.tests(isAssigned())) return (T) this;
		
		final NavigableSet<VersionEnumerable<Subject>> pras = previousRuntimeAssigneds();
		return pras.isEmpty()
				? Elemental.get(()-> previous(), ()-> (T) this)
				: (T) pras.first();
	}
	
	/**
	 * @param <T>
	 * @return non-null
	 */
	default public <T extends VersionEnumerable<Subject>> NavigableSet<T> previousRuntimeAssigneds() {
		final NavigableSet<T> prs = previousRuntimes();
		if (prs == null) return Collections.emptyNavigableSet();
		
		NavigableSet<T> pras = new TreeSet<>(prs);
		for (T pr : prs) 
			if (!Elemental.tests(pr.isAssigned())) pras.remove(pr);

		// previous runtimes' previousRuntimeAssigneds()
		if (pras.isEmpty()) for (T pr : prs) {
			pras = pr.previousRuntimeAssigneds();
			if (pras.isEmpty()) continue;
		}
		return pras;
	}

//	@Override
//	default public Assignable<?> getAssignable() {
//		return isInAST()
//				? AssignableElement.super.getAssignable()
//				: null;
//	}
	
	
	
	@Override
	default public IASTNode getASTAddress() {
		return AssignableElement.getAsn(()-> 
		getAssignable().getASTAddress());
	}
	
	@Override
	default String getShortAddress() {
		return isInAST()
				? ASTAddressable.super.getShortAddress()
				: getName();
	}
	
	public VODCondGen getCondGen();

//	public NavigableSet<OmpDirective> getEnclosingDirectives();
	public List<IASTStatement> getDependentLoops();
	
//	default public Subject getSubject() {
//		try {
//			return getVersion().getSubject();
//		} catch (ReenterException | IncomparableException | UncertainPlaceholderException | NoSuchVersionException e) {
//			return null;
//		}
//	}
	
	public String getName();
	public PlatformType getType();
	
	/**
	 * @return the indirect variable/function subject but not direct version reference.
	 * 	This is distinguished from {@link VersionPlaceholder#getSubject()}.
	 */
	default public Subject getVersionSubject() {
		return getVersion().getSubject();
	}
	
	/**
	 * @return the current version with initialization or reversion,
	 * 	therefore it may <em>not</em> be null.
	 */
	default public Version<? extends Subject> getVersion() {
		return Elemental.get(()-> peekVersion(),
				()-> DebugElement.throwTodoException("unsupported operation"));
	}
	default public Version<? extends Subject> getVersion(FunctionallableRole role) {
		return Elemental.get(()-> peekVersion(role),
				()-> DebugElement.throwTodoException("unsupported operation"));
	}
	
	/**
	 * @return the current version without initialization nor reversion,
	 * 	therefore it may be null.
	 */
	public Version<? extends Subject> peekVersion();
	default public Version<? extends Subject> peekVersion(ThreadRoleMatchable role) {
		return role == null
				? null
				: DebugElement.throwTodoException("unsupported role");
	}
	
	/**
	 * Replacing current version without checking inter-version compliance.
	 * @param newVersion
	 * @throws NoSuchVersionException 
	 */
	default public void setVersion(Version<? extends Subject> newVersion) throws NoSuchVersionException {
		DebugElement.throwTodoException("unsupported operation");
	}
	
	default public boolean reversions() {
		return !Elemental.testsNot(isAssigned());	// null or isAssigned
	}
	
	default public void reversion(Version<? extends Subject> newVersion) throws NoSuchVersionException {
		if (!reversions()) return;
//		else throwTodoException("in-reversionable VersionEnumerable");
	}

}