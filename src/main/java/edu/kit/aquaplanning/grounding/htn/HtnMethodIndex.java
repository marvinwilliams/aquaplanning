package edu.kit.aquaplanning.grounding.htn;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.function.Function;

import edu.kit.aquaplanning.grounding.datastructures.ArgumentAssignment;
import edu.kit.aquaplanning.grounding.datastructures.LiftedState;
import edu.kit.aquaplanning.model.ground.Precondition;
import edu.kit.aquaplanning.model.ground.htn.Reduction;
import edu.kit.aquaplanning.model.lifted.Argument;
import edu.kit.aquaplanning.model.lifted.Operator;
import edu.kit.aquaplanning.model.lifted.PlanningProblem;
import edu.kit.aquaplanning.model.lifted.condition.AbstractCondition;
import edu.kit.aquaplanning.model.lifted.condition.Condition;
import edu.kit.aquaplanning.model.lifted.condition.ConditionSet;
import edu.kit.aquaplanning.model.lifted.htn.Constraint;
import edu.kit.aquaplanning.model.lifted.htn.Method;
import edu.kit.aquaplanning.model.lifted.htn.Task;

public class HtnMethodIndex {

	private PlanningProblem p;
	
	private Set<String> primitiveTaskNames;
	private Set<String> actionStrings;
	private LiftedState convergedState;	
	
	private Map<Method, List<Reduction>> reductions;
	
	private class PartiallyGroundMethod {
		ArgumentAssignment assignment;
		Method method;
		public PartiallyGroundMethod(ArgumentAssignment assignment, Method method) {
			this.assignment = assignment;
			this.method = method;
		}
	}
	
	public HtnMethodIndex(PlanningProblem p, LiftedState convergedState, List<Operator> instantiatedOperators) {
		
		this.p = p;
		this.primitiveTaskNames = new HashSet<>();
		this.actionStrings = new HashSet<>();
		
		this.convergedState = convergedState;
		for (Operator op : instantiatedOperators) {
			primitiveTaskNames.add(op.getName());
			actionStrings.add(op.toActionString());
		}

		this.reductions = new HashMap<>();
	}
	
	public List<Reduction> getRelevantReductions(List<Method> methods, Function<AbstractCondition, Precondition> conditionGrounder) {
		
		List<Reduction> reductions = new ArrayList<>();
		for (Method m : methods) {
			reductions.addAll(getRelevantReductions(m, conditionGrounder));
		}
		return reductions;
	}
	
	public List<Reduction> getRelevantReductions(Method m, Function<AbstractCondition, Precondition> conditionGrounder) {
		
		List<Reduction> newReductions = new ArrayList<>();
		
		if (reductions.containsKey(m)) {
			return reductions.get(m);
		}
		if (!checkConsistency(m)) {
			return new ArrayList<>();
		}
		if (m.getImplicitArguments().size() == 0) {
			newReductions.add(new Reduction(m, conditionGrounder));
			reductions.put(m, newReductions);
			return newReductions;
		}
		
		List<List<Argument>> eligibleConstants = new ArrayList<>();
		for (Argument arg : m.getImplicitArguments()) {
			List<Argument> constants = new ArrayList<>();
			for (Argument constant : p.getConstants()) {
				if (p.isArgumentOfType(constant, arg.getType())) {
					constants.add(constant);
				}
			}
			eligibleConstants.add(constants);
		}
			
		Map<String, Integer> argIndices = new HashMap<>();
		int pos = 0;
		for (Argument arg : m.getImplicitArguments()) {
			argIndices.put(arg.getName(), pos++);
		}
		
		List<Argument> sortedArgs = new ArrayList<>();
		sortedArgs.addAll(m.getImplicitArguments());
		Map<Argument, Integer> argOccurrences = getArgumentOccurrences(m);
		int[] orderedArgIndices = new int[m.getImplicitArguments().size()];
		sortedArgs.sort((arg1, arg2) -> {
			// Sort arguments in decreasing order by the amount 
			// of occurrences in constraints and subtasks
			int occ1 = argOccurrences.get(arg1);
			int occ2 = argOccurrences.get(arg2);
			return occ2 - occ1;
		});
		int idx = 0;
		for (Argument arg : sortedArgs) {
			orderedArgIndices[idx++] = argIndices.get(arg.getName());
		}
		
		List<Argument> implicitArgs = m.getImplicitArguments();
		ArgumentAssignment initAssignment = new ArgumentAssignment(implicitArgs.size());
		Stack<PartiallyGroundMethod> assignmentStack = new Stack<>();
		assignmentStack.push(new PartiallyGroundMethod(initAssignment, 
				m.getMethodBoundToArguments(m.getExplicitArguments(), m.getImplicitArguments())));
		
		while (!assignmentStack.isEmpty()) {
			
			PartiallyGroundMethod pgm = assignmentStack.pop();
			ArgumentAssignment assignment = pgm.assignment;
			Method method = pgm.method;
			if (assignment.getDecisionLevel() == implicitArgs.size()) {
				
				// Finished
				try {
					newReductions.add(new Reduction(method, conditionGrounder));
				} catch (IllegalArgumentException e) {
					continue;
				}
				
			} else {
				
				// Choose an argument assignment
				int argPos = orderedArgIndices[assignment.getDecisionLevel()];
				Argument arg = implicitArgs.get(argPos);
				for (Argument constant : eligibleConstants.get(argPos)) {	
					PartiallyGroundMethod newPgm = extendAssignment(pgm, argPos, arg, constant);
					if (newPgm != null) {
						assignmentStack.push(newPgm);
					}
				}
			}
		}
		
		reductions.put(m, newReductions);
		return newReductions;
	}
	
	private PartiallyGroundMethod extendAssignment(PartiallyGroundMethod pgm, int argPos, Argument refArg, Argument argVal) {
		
		ArgumentAssignment newAssignment = new ArgumentAssignment(pgm.assignment);
		newAssignment.set(argPos, argVal);
		Method newMethod = pgm.method.copy();
		newMethod.setImplicitArgument(refArg, argVal);
		
		boolean consistent = checkConsistency(newMethod);
		if (consistent) {
			return new PartiallyGroundMethod(newAssignment, newMethod);
		} else return null;
	}
	
	private boolean checkConsistency(Method newMethod) {
			
		// If the method contains any primitive tasks,
		// see if the respective action occurs in the problem
		for (Task t : newMethod.getSubtasks()) {
			if (primitiveTaskNames.contains(t.getName())) {
				// Subtask is primitive
				if (t.getArguments().stream().allMatch(arg -> arg.isConstant())) {
					// Subtask is fully instantiated
					if (!actionStrings.contains(t.toTaskString())) {
						// Action does not occur
						return false;
					}
				}
			}
		}
		
		// If the method contains any constraints,
		// see if all pos. conditions exist in the lifted superstate
		for (Constraint c : newMethod.getConstraints()) {
			AbstractCondition cond = c.getCondition();
			List<AbstractCondition> conditions = new ArrayList<>();
			conditions.add(cond);
			for (int i = 0; i < conditions.size(); i++) {
				cond = conditions.get(i);
				switch (cond.getConditionType()) {
				case atomic:
					Condition atom = (Condition) cond;
					if (atom.getArguments().stream().anyMatch(arg -> !arg.isConstant())) {
						// Condition is not fully instantiated
						continue;
					}
					if (!convergedState.holds(atom)) {
						return false;
					}
					break;
				case conjunction:
					conditions.addAll(((ConditionSet) cond).getConditions());
					break;
				default:
					break;
				}
			}
		}
		
		return true;
	}
	
	private Map<Argument, Integer> getArgumentOccurrences(Method m) {
		
		Map<Argument, Integer> argOccurrences = new HashMap<>();
		for (Argument arg : m.getExplicitArguments())
			argOccurrences.put(arg, 0);
		for (Argument arg : m.getImplicitArguments())
			argOccurrences.put(arg, 0);
		
		for (Task t : m.getSubtasks()) {
			if (primitiveTaskNames.contains(t.getName())) {
				for (Argument arg : t.getArguments()) {
					argOccurrences.put(arg, argOccurrences.getOrDefault(arg,0)+1);
				}
			}
		}
		for (Constraint c : m.getConstraints()) {
			AbstractCondition cond = c.getCondition();
			List<AbstractCondition> conditions = new ArrayList<>();
			conditions.add(cond);
			for (int i = 0; i < conditions.size(); i++) {
				cond = conditions.get(i);
				switch (cond.getConditionType()) {
				case atomic:
					Condition atom = (Condition) cond;
					for (Argument arg : atom.getArguments()) {
						argOccurrences.put(arg, argOccurrences.getOrDefault(arg,0)+1);
					}
					break;
				case conjunction:
					conditions.addAll(((ConditionSet) cond).getConditions());
					break;
				default:
					break;
				}
			}
		}
		return argOccurrences;
	}
}