package edu.kit.aquaplanning.planning;

import java.util.List;
import java.util.Map;

import edu.kit.aquaplanning.Configuration;
import edu.kit.aquaplanning.model.ground.Action;
import edu.kit.aquaplanning.model.ground.Atom;
import edu.kit.aquaplanning.model.ground.GroundPlanningProblem;
import edu.kit.aquaplanning.model.ground.Plan;
import edu.kit.aquaplanning.model.lifted.PlanningProblem;
import edu.kit.aquaplanning.sat.SatSolver;

public class LiftedSatPlanner extends LiftedPlanner {

  public LiftedSatPlanner(Configuration config) {
    super(config);
  }

  @Override
  public Plan findPlan(PlanningProblem problem) {
    // initialize the SAT solver
    SatSolver solver = new SatSolver();
    addInitialState(p, solver);

    // find the plan
    int step = 0;
    while (true) {

      if (solver.isSatisfiable(assumptions)) {
        break;
      }
      if (!withinComputationalBounds(step + 1)) {
        // No plan found in the given computational bounds
        return null;
      }
      step++;
    }

    // Decode the plan
    Plan plan = new Plan();
    int[] model = solver.getModel();
    return plan;
  }

  protected void addInitialState(PlanningProblem p, SatSolver solver) {
    p.get
  }

  protected int maxParameters;
  protected int numVariables;
  protected int numOperators;
  protected int num
}
