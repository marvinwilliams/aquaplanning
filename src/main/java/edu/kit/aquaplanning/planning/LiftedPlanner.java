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
    case forwardSSS:
      return null;
    case satBased:
      return null;
    case hegemannSat:
      return null;
    case parallel:
      return null;
    case liftedSat:
      return new LiftedSatPlanner(config);
    default:
      return null;
    }
  }

  @Override
  public String toString() {
    return getClass().toString();
  }
}
