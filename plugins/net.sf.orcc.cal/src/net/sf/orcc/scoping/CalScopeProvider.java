/*
 * generated by Xtext
 */
package net.sf.orcc.scoping;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import net.sf.orcc.cal.Action;
import net.sf.orcc.cal.Actor;
import net.sf.orcc.cal.Function;
import net.sf.orcc.cal.Generator;
import net.sf.orcc.cal.InputPattern;
import net.sf.orcc.cal.ListExpression;
import net.sf.orcc.cal.Procedure;
import net.sf.orcc.cal.Variable;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EReference;
import org.eclipse.xtext.scoping.IScope;
import org.eclipse.xtext.scoping.IScopedElement;
import org.eclipse.xtext.scoping.impl.AbstractDeclarativeScopeProvider;
import org.eclipse.xtext.scoping.impl.ScopedElement;
import org.eclipse.xtext.scoping.impl.SimpleScope;

/**
 * This class contains custom scoping description.
 * 
 * see : http://www.eclipse.org/Xtext/documentation/latest/xtext.html#scoping on
 * how and when to use it
 * 
 */
public class CalScopeProvider extends AbstractDeclarativeScopeProvider {

	/**
	 * Returns the scope for a variable referenced inside an action. An action
	 * is a bit different because it has its input patterns in addition to its
	 * local variables.
	 * 
	 * @param action
	 *            an action
	 * @param ref
	 *            unknown!
	 * @return a scope
	 */
	private IScope getScope(Action action, EReference ref) {
		List<IScopedElement> elements = new ArrayList<IScopedElement>();
		for (InputPattern pattern : action.getInputs()) {
			for (Variable token : pattern.getTokens()) {
				IScopedElement element = ScopedElement.create(token.getName(),
						token);
				elements.add(element);
			}
		}

		for (Variable variable : action.getVariables()) {
			IScopedElement element = ScopedElement.create(variable.getName(),
					variable);
			elements.add(element);
		}

		IScope outer = getScope(action.eContainer(), ref);
		IScope scope = new SimpleScope(outer, elements);
		return scope;
	}

	/**
	 * Returns the scope for a variable referenced inside a function/procedure.
	 * 
	 * @param parameters
	 *            a list of parameters
	 * @param variables
	 *            a list of variables
	 * @param ref
	 *            unknown!
	 * @return a scope
	 */
	private IScope getScope(List<Variable> parameters,
			List<Variable> variables, EObject obj, EReference ref) {
		List<IScopedElement> elements = new ArrayList<IScopedElement>();
		for (Variable variable : parameters) {
			IScopedElement element = ScopedElement.create(variable.getName(),
					variable);
			elements.add(element);
		}

		for (Variable variable : variables) {
			IScopedElement element = ScopedElement.create(variable.getName(),
					variable);
			elements.add(element);
		}

		IScope outer = getScope(obj.eContainer(), ref);
		IScope scope = new SimpleScope(outer, elements);
		return scope;
	}

	/**
	 * Returns the scope for a variable referenced inside an action.
	 * 
	 * @param action
	 *            an action
	 * @param ref
	 *            unknown!
	 * @return a scope
	 */
	public IScope scope_VariableReference_variable(Action action, EReference ref) {
		return getScope(action, ref);
	}

	/**
	 * Returns the scope for a variable referenced inside an actor.
	 * 
	 * @param actor
	 *            an actor
	 * @param ref
	 *            unknown!
	 * @return a scope
	 */
	public IScope scope_VariableReference_variable(Actor actor, EReference ref) {
		List<IScopedElement> elements = new ArrayList<IScopedElement>();
		for (Variable parameter : actor.getParameters()) {
			IScopedElement element = ScopedElement.create(parameter.getName(),
					parameter);
			elements.add(element);
		}

		for (Variable stateVariable : actor.getStateVariables()) {
			IScopedElement element = ScopedElement.create(stateVariable
					.getName(), stateVariable);
			elements.add(element);
		}

		IScope scope = new SimpleScope(elements);
		return scope;
	}

	/**
	 * Returns the scope for a variable referenced inside a function.
	 * 
	 * @param func
	 *            a function
	 * @param ref
	 *            unknown!
	 * @return a scope
	 */
	public IScope scope_VariableReference_variable(Function func, EReference ref) {
		return getScope(func.getParameters(), func.getVariables(), func, ref);
	}

	/**
	 * Returns the scope for a variable referenced inside a generator.
	 * 
	 * @param list
	 *            a list expression
	 * @param ref
	 *            unknown!
	 * @return a scope
	 */
	@SuppressWarnings("unchecked")
	public IScope scope_VariableReference_variable(ListExpression list,
			EReference ref) {
		List<Variable> variables = new ArrayList<Variable>();
		for (Generator generator : list.getGenerators()) {
			variables.add(generator.getVariable());
		}
		return getScope(variables, Collections.EMPTY_LIST, list, ref);
	}

	/**
	 * Returns the scope for a variable referenced inside a procedure.
	 * 
	 * @param proc
	 *            a procedure
	 * @param ref
	 *            unknown!
	 * @return a scope
	 */
	public IScope scope_VariableReference_variable(Procedure proc,
			EReference ref) {
		return getScope(proc.getParameters(), proc.getVariables(), proc, ref);
	}

}
