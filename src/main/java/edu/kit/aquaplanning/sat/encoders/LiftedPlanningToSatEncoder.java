package edu.kit.aquaplanning.sat.encoders;

import java.util.List;

import edu.kit.aquaplanning.grounding.PlanningGraphGrounder;
import edu.kit.aquaplanning.model.ground.Plan;
import edu.kit.aquaplanning.model.lifted.PlanningProblem;
import edu.kit.aquaplanning.sat.SymbolicReachabilityFormula;

public interface LiftedPlanningToSatEncoder {
	/**
	 * Encode a planning problem into 4 sat formulas
	 * @param problem
	 * @return
	 */
	public SymbolicReachabilityFormula encodeProblem(PlanningProblem problem, PlanningGraphGrounder grounder);

	/**
	 * @param problem
	 * @param model
	 * @return
	 */
	public Plan decodePlan(List<int[]> model);

}
