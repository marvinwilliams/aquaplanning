package edu.kit.aquaplanning.planning;

import edu.kit.aquaplanning.Configuration;
import edu.kit.aquaplanning.model.ground.GroundPlanningProblem;
import edu.kit.aquaplanning.model.ground.Plan;
import edu.kit.aquaplanning.util.Logger;

/**
 * Blueprint for a planner operating on a fully grounded planning problem.
 * 
 * @author Dominik Schreiber
 */
public abstract class GroundPlanner extends Planner {

  public GroundPlanner(Configuration config) {
    super(config);
    this.isGrounded = true;
  }

  /**
   * Attempt to find a solution plan for the provided problem.
   */
  public abstract Plan findPlan(GroundPlanningProblem problem);

  public static GroundPlanner getPlanner(Configuration config) {
    switch (config.plannerType) {
    case forwardSSS:
      return new ForwardSearchPlanner(config);
    case satBased:
      return new SimpleSatPlanner(config);
    case hegemannSat:
      return new HegemannsSatPlanner(config);
    case parallel:
      Logger.log(Logger.INFO, "Doing parallel planning with up to " + config.numThreads + " threads.");
      return new PortfolioParallelPlanner(config);
    case liftedSat:
      return null;
    default:
      return null;
    }
  }

  @Override
  public String toString() {
    return getClass().toString();
  }
}
