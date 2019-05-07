package edu.kit.aquaplanning.sat.encoders;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.kit.aquaplanning.grounding.PlanningGraphGrounder;
import edu.kit.aquaplanning.model.ground.Action;
import edu.kit.aquaplanning.model.ground.Atom;
import edu.kit.aquaplanning.model.ground.GroundPlanningProblem;
import edu.kit.aquaplanning.model.ground.Plan;
import edu.kit.aquaplanning.model.lifted.PlanningProblem;
import edu.kit.aquaplanning.sat.SatFormula;
import edu.kit.aquaplanning.sat.SymbolicReachabilityFormula;

public class LiftedEncoding implements LiftedPlanningToSatEncoder {

  @Override
  public SymbolicReachabilityFormula encodeProblem(PlanningProblem problem, PlanningGraphGrounder grounder) {
    SymbolicReachabilityFormula srp = new SymbolicReachabilityFormula();
    initializeActionIdsAndSupports(problem);
    srp.goalConditions = getGoalAssumptions(problem);
    srp.initialConditions = getInitialStateClauses(problem);
    srp.transitionClauses = getTransitionalClauses(problem);
    srp.universalClauses = getUniversalClauses(problem);
    return srp;
  }

  @Override
  public Plan decodePlan(List<int[]> model) {
    initializeActionIdsAndSupports(problem);
    Plan plan = new Plan();
    for (int i = 0; i < model.size(); i++) {
      for (Action a : problem.getActions()) {
        if (model.get(i)[getActionSatVariable(a.getName(), 0)] > 0) {
          plan.appendAtBack(a);
        }
      }
    }
    return plan;
  }

  protected int[] getGoalAssumptions(PlanningProblem problem) {
    ConditionSet goalSet = new ConditionSet(ConditionType.conjunction);
    problem.getGoals().forEach(c -> goalSet.add(c));
    Pair<ConditionSet, ConditionSet> split = grounder.splitCondition(goalSet);
    ConditionSet simpleSet = split.getLeft();
    goalClause = new int[simpleSet.getConditions().size()];
    int counter = 0;
    for (AbstractCondition c : simpleSet.getConditions()) {
      Condition goal = (Condition) c;
      if (goal.isNegated()) {
        goalClause[counter++] = -getPredicateSatId(predicates.get(goal.withoutNegation()), false);
      } else {
        goalClause[counter++] = getPredicateSatId(predicates.get(goal), false);
      }
    }
    // System.out.println("Goal: " + goalClause);
  }
}
