package edu.kit.aquaplanning.planning;

import edu.kit.aquaplanning.Configuration;
import edu.kit.aquaplanning.model.ground.Plan;
import edu.kit.aquaplanning.model.lifted.PlanningProblem;

/**
 * Blueprint for a planner operating on the lifted problem.
 * 
 * @author Dominik Schreiber
 */
public abstract class LiftedPlanner extends Planner {

  public LiftedPlanner(Configuration config) {
    super(config);
    this.isGrounded = false;
  }

  /**
   * Attempt to find a solution plan for the provided problem.
   */
  public abstract Plan findPlan(PlanningProblem problem);

  public static LiftedPlanner getPlanner(Configuration config) {
    switch (config.plannerType) {
    case pLiftedSat:
      return new PureLiftedSatPlanner(config);
    case gLiftedSat:
      return new GroundLiftedSatPlanner(config);
    case hLiftedSat:
      return new HelperLiftedSatPlanner(config);
    default:
      return null;
    }
  }

  @Override
  public String toString() {
    return getClass().toString();
  }
}
