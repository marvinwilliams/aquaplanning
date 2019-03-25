package edu.kit.aquaplanning.grounding;

import java.util.ArrayList;
import java.util.List;

import edu.kit.aquaplanning.model.lifted.Argument;
import edu.kit.aquaplanning.model.lifted.PlanningProblem;
import edu.kit.aquaplanning.model.lifted.Type;

/**
 * Provides some tools for full iteration over possible argument
 * combinations under certain constraints.
 */
public class ArgumentCombinationUtils {
	
	/**
	 * Given a list of possible values at each index,
	 * allows to iterate over all possible combinations.
	 */
    
	public static class Iterator<T> implements java.util.Iterator<List<T>> {
		
		private List<List<T>> eligible;
		private List<Integer> currentIndices;
		private boolean hasNext;
		
		/**
		 * @param eligible At index i, contains a list of all eligible
		 * values for the position i.
		 */
		public Iterator(List<List<T>> eligible) {
			
			this.eligible = eligible;

			// Set current value indices to zero
			// (first combination)
			currentIndices = new ArrayList<>();
			hasNext = true;
			for (int i = 0; i < eligible.size(); i++) {
				if (eligible.get(i).isEmpty())
					// no value at position i to choose from
					hasNext = false; 
				currentIndices.add(0);
			}
		}
		
		/**
		 * True, iff there is another combination not retrieved yet.
		 */
		@Override
		public boolean hasNext() {
			return hasNext;
		}
		
		/**
		 * Get the next combination.
		 */
		@Override
		public List<T> next() {
			
			// Create current combination
			List<T> values = new ArrayList<>();
			int valPos = 0;
			for (int idx : currentIndices) {
				values.add(eligible.get(valPos++).get(idx));
			}
			
			// Get to next combination, if possible
			hasNext = false;
			for (int pos = currentIndices.size()-1; pos >= 0; pos--) {
				
				// Are there more options at this position?
				if (currentIndices.get(pos)+1 < eligible.get(pos).size()) {
					// -- Yes
					
					// Proceed to the next option at this position
					currentIndices.set(pos, currentIndices.get(pos)+1);
					
					// Reset all succeeding options to zero
					for (int posAfter = pos+1; posAfter < currentIndices.size(); posAfter++) {
						currentIndices.set(posAfter, 0);
					}
					
					hasNext = true;
					break;
				}
			}
			
			return values;
		}
	}
	
	public static <T> Iterator<T> iterator(List<List<T>> eligible) {
		return new Iterator<T>(eligible);
	}
	
	/**
	 * For a list of arguments, returns a list containing all valid
	 * argument combinations which can be retrieved by
	 * replacing each variable in the arguments by a
	 * constant of an appropriate type.
	 * This list of eligible arguments may have been shortened
	 * by applying simplification strategies.
	 */
	public static List<List<Argument>> getEligibleArguments(List<Argument> args,
			PlanningProblem problem, List<Argument> allConstants) {
		
		List<Type> argTypes = new ArrayList<>();
		for (Argument arg : args) {
			argTypes.add(arg.getType());
		}
		return getEligibleArgumentsOfType(argTypes, problem, allConstants);
	}
	
	/**
	 * Returns each possible combination of constants with the 
	 * provided order of types.
	 */
	public static List<List<Argument>> getEligibleArgumentsOfType(List<Type> argTypes, 
			PlanningProblem problem, List<Argument> allConstants) {
		
		List<List<Argument>> eligibleArguments = new ArrayList<>();
		
		// For each provided type
		for (Type argType : argTypes) {
			List<Argument> eligibleArgumentsAtPos = new ArrayList<>();
			
			// For all possible constants at the argument position
			for (Argument c : allConstants) {
				if (problem.isArgumentOfType(c, argType)) {
					
					eligibleArgumentsAtPos.add(c);
				}
			}
			
			eligibleArguments.add(eligibleArgumentsAtPos);
		}
		
		return eligibleArguments;
	}	
}
