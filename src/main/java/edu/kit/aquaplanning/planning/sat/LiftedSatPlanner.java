package edu.kit.aquaplanning.planning.sat;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import edu.kit.aquaplanning.Configuration;
import edu.kit.aquaplanning.grounding.PlanningGraphGrounder;
import edu.kit.aquaplanning.model.ground.ActionPlan;
import edu.kit.aquaplanning.model.ground.GroundPlanningProblem;
import edu.kit.aquaplanning.model.lifted.Argument;
import edu.kit.aquaplanning.model.lifted.Operator;
import edu.kit.aquaplanning.model.lifted.PlanningProblem;
import edu.kit.aquaplanning.model.lifted.Predicate;
import edu.kit.aquaplanning.model.lifted.condition.AbstractCondition;
import edu.kit.aquaplanning.model.lifted.condition.AbstractCondition.ConditionType;
import edu.kit.aquaplanning.model.lifted.condition.Condition;
import edu.kit.aquaplanning.model.lifted.condition.ConditionSet;
import edu.kit.aquaplanning.planning.LiftedPlanner;
import edu.kit.aquaplanning.sat.SymbolicReachabilityFormula;
import edu.kit.aquaplanning.util.Logger;
import edu.kit.aquaplanning.util.Pair;

public class LiftedSatPlanner extends LiftedPlanner {

  public LiftedSatPlanner(Configuration config) {
    super(config);
  }

  public List<Boolean> computeGroundArguments(Operator operator, List<Integer> numArguments) {
    return null;
  }

  public List<Operator> getPartiallyLiftedOperators(List<Operator> liftedOperators, List<Operator> groundedOperators) {
    Map<String, Integer> operatorIndex = new HashMap<String, Integer>();
    List<List<Set<Argument>>> operatorArgs = new ArrayList<List<Set<Argument>>>();
    // Set up the lookup to the lifted operators
    for (Operator o : liftedOperators) {
      String name = o.getName();
      operatorIndex.put(name, operatorIndex.size());
      List<Set<Argument>> args = new ArrayList<Set<Argument>>();
      for (int i = 0; i < o.getArguments().size(); i++) {
        args.add(new HashSet<Argument>());
      }
      operatorArgs.add(args);
    }
    // List the sets of arguments of the lifted operators to determine the arguments
    // to ground
    for (Operator o : groundedOperators) {
      int idx = operatorIndex.get(o.getName());
      for (int i = 0; i < o.getArguments().size(); i++) {
        operatorArgs.get(idx).get(i).add(o.getArguments().get(i));
      }
    }
    // Get the list of grounded arguments
    List<List<Boolean>> operatorArgumentsToGround = new ArrayList<>();
    for (Operator o : liftedOperators) {
      int idx = operatorIndex.get(o.getName());
      List<Integer> numArgs = new ArrayList<Integer>();
      for (int i = 0; i < o.getArguments().size(); i++) {
        numArgs.add(operatorArgs.get(idx).get(i).size());
      }
      operatorArgumentsToGround.add(computeGroundArguments(o, numArgs));
    }
    Set<Operator> partiallyGroundedOperators = new HashSet<Operator>();
    // Get the partially grounded operator for each grounded operator
    for (Operator o : groundedOperators) {
      int idx = operatorIndex.get(o.getName());
      Operator liftedOperator = liftedOperators.get(idx);
      List<Argument> args = new ArrayList<>();
      for (int i = 0; i < o.getArguments().size(); i++) {
        if (operatorArgumentsToGround.get(idx).get(i)) {
          args.add(o.getArguments().get(i));
        } else {
          args.add(null);
        }
      }
      partiallyGroundedOperators.add(liftedOperator.getOperatorWithGroundArguments(args));
    }
    return partiallyGroundedOperators.stream().collect(Collectors.toList());
  }

  @Override
  public ActionPlan plan(PlanningProblem problem) {
    PlanningGraphGrounder grounder = new PlanningGraphGrounder(config);
    GroundPlanningProblem groundedProblem = grounder.ground(problem);

    Map<String, Integer> operatorIndex = new HashMap<String, Integer>();
    List<List<Boolean>> groundedArgumentPositions = new ArrayList<List<Boolean>>();
    {
      List<Set<List<Argument>>> argumentCombinations = new ArrayList<Set<List<Argument>>>();
      List<List<Set<Argument>>> eligibleArguments = new ArrayList<List<Set<Argument>>>();
      for (Operator o : problem.getOperators()) {
        String name = o.getName();
        operatorIndex.put(name, operatorIndex.size());
        argumentCombinations.add(new HashSet<List<Argument>>());
      }
      Set<Predicate> conditions = new HashSet<Predicate>();
      for (Operator o : grounder.getFilteredActions()) {
        int oIndex = operatorIndex.get(o.getName());
        argumentCombinations.get(oIndex).add(o.getArguments());
        for (int i = 0; i < o.getArguments().size(); i++) {
          eligibleArguments.get(oIndex).get(i).add(o.getArguments().get(i));
        }
      }
      for (Operator o : problem.getOperators()) {
        List<Integer> numArguments = new ArrayList<Integer>();
        for (Set<Argument> args : eligibleArguments.get(operatorIndex.get(o.getName()))) {
          numArguments.add(args.size());
        }
        groundedArgumentPositions.add(computeGroundArguments(o, numArguments));
      }
    }
    List<Set<List<Argument>>> argumentCombinations = new ArrayList<Set<List<Argument>>>();
    List<List<Set<Argument>>> eligibleArguments = new ArrayList<List<Set<Argument>>>();
    for (Operator o : grounder.getFilteredActions()) {
      int liftedIndex = operatorIndex.get(o.getName());
      Operator partiallyGroundedOperator = problem.getOperators().get(liftedIndex);
      List<Argument> groundArgs = new ArrayList<Argument>();
      for (int i = 0; i < o.getArguments().size(); i++) {
        if (groundedArgumentPositions.get(liftedIndex).get(i)) {
          groundArgs.add(o.getArguments().get(i));
        } else {
          groundArgs.add(null);
        }
        partiallyGroundedOperator.getOperatorWithGroundArguments(groundArgs);
        // TODO add lifted arguments to possible args of partially grounded;
      }
    }
    {
      Pair<ConditionSet, ConditionSet> split = grounder.splitCondition(o.getPrecondition());
      if (!split.getRight().getConditions().isEmpty()) {
        Logger.log(Logger.WARN, "Operator " + o.toString() + " has complex preconditions");
      }
      for (AbstractCondition c : split.getLeft().getConditions()) {
        if (c.getConditionType() != ConditionType.atomic) {
          Logger.log(Logger.WARN, "Condition " + c + " is expected to be atomic");
        }
        preconditions.add((Condition) c);
      }
    }
    {
      Pair<ConditionSet, ConditionSet> split = grounder.splitCondition(o.getEffect());
      if (!split.getRight().getConditions().isEmpty()) {
        Logger.log(Logger.WARN, "Operator " + o.toString() + " has complex preconditions");
      }
      for (AbstractCondition c : split.getLeft().getConditions()) {
        if (c.getConditionType() != ConditionType.atomic) {
          Logger.log(Logger.WARN, "Condition " + c + " is expected to be atomic");
        }
        preconditions.add((Condition) c);
      }
    }
    for (Operator o : problem.getOperators()) {
    }
    return null;
  }

  private SymbolicReachabilityFormula encoding;
  private List<Operator> partiallyGroundedOperators;
  private Set<Condition> preconditions;
  private Set<Condition> effects;

}
