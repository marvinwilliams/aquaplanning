package edu.kit.aquaplanning.planning;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiPredicate;

import edu.kit.aquaplanning.Configuration;
import edu.kit.aquaplanning.grounding.ArgumentCombinationUtils;
import edu.kit.aquaplanning.grounding.RelaxedPlanningGraphGrounder;
import edu.kit.aquaplanning.model.ground.Plan;
import edu.kit.aquaplanning.model.lifted.Argument;
import edu.kit.aquaplanning.model.lifted.Operator;
import edu.kit.aquaplanning.model.lifted.PlanningProblem;
import edu.kit.aquaplanning.model.lifted.condition.AbstractCondition;
import edu.kit.aquaplanning.model.lifted.condition.AbstractCondition.ConditionType;
import edu.kit.aquaplanning.model.lifted.condition.Condition;
import edu.kit.aquaplanning.model.lifted.condition.ConditionSet;
import edu.kit.aquaplanning.sat.SatSolver;
import edu.kit.aquaplanning.util.Logger;
import edu.kit.aquaplanning.util.Pair;

public class GroundLiftedSatPlanner extends LiftedPlanner {

  public GroundLiftedSatPlanner(Configuration config) {
    super(config);
  }

  @Override
  public Plan findPlan(PlanningProblem p) {
    problem = p;
    Logger.log(Logger.INFO, "TIME0 Generate clauses");
    grounder = new RelaxedPlanningGraphGrounder(config);
    graph = grounder.computeGraph(p);
    isGrounded = (o, a) -> a.getName().startsWith("?_nono");
    Logger.log(Logger.INFO, "TIME1");
    // initialize the SAT solver
    SatSolver solver = new SatSolver();
    initIDs();
    generateClauses();

    int step = 0;

    for (int[] clause : initialClauses) {
      solver.addClause(clause);
    }
    Logger.log(Logger.INFO, "TIME2 Starting solver");
    while (true) {
      for (int[] clause : universalClauses) {
        solver.addClause(clause);
      }
      if (solver.isSatisfiable(goalClause)) {
        Logger.log(Logger.INFO, "TIME3 Solution found in step " + step);
        break;
      }
      Logger.log(Logger.INFO, "No solution found in step " + step);
      for (int[] clause : transitionClauses) {
        solver.addClause(clause);
      }
      nextStep();
      step++;
    }
    grounder.ground(problem);
    return extractPlan(solver.getModel(), step);
  }

  protected Plan extractPlan(int[] model, int steps) {
    Plan plan = new Plan();
    for (int base = 0; base < steps * stepVars; base += stepVars) {
      for (Operator o : operators.keySet()) {
        int i = operators.get(o);
        if (model[getOperatorSatId(i) + base] > 0) {
          List<Argument> args = new ArrayList<>();
          for (int j = 0; j < o.getArguments().size(); j++) {
            if (o.getArguments().get(j).isConstant()) {
              args.add(null);
              continue;
            }
            boolean found = eligibleArguments.get(i).get(j).size() == 0;
            for (Argument arg : eligibleArguments.get(i).get(j).keySet()) {
              int k = eligibleArguments.get(i).get(j).get(arg);
              if (model[getParameterSatId(i, j, k) + base] >= 0) {
                args.add(arg);
                found = true;
                break;
              }
            }
            if (!found) {
              Logger.log(Logger.ERROR, "Parameter not set in solution");
              System.exit(1);
            }
          }
          Operator go = o.getOperatorWithGroundArguments(args);
          plan.appendAtBack(grounder.getAction(go));
        }
      }
    }
    return plan;
  }

  protected void initIDs() {
    satCounter = 1;
    setPredicateIDs();
    setOperatorIDs();
    forbidden = new HashSet<>();
    for (Operator operator : operators.keySet()) {
      for (AbstractCondition ac : Arrays.asList(operator.getPrecondition(), operator.getEffect())) {
        ConditionSet simpleSet = grounder.splitCondition(ac).getLeft();
        for (AbstractCondition c : simpleSet.getConditions()) {
          if (c.getConditionType() != ConditionType.atomic) {
            Logger.log(Logger.ERROR, "A simple set of conditions contains non-atomic condition " + c + ".");
            System.exit(1);
          }
          Condition condition = (Condition) c;
          setForbiddenConditions(operator, condition);
        }
      }
    }
    Logger.log(Logger.INFO, "Number of predicates: " + predicates.size());
    Logger.log(Logger.INFO, "Number of operators: " + operators.size());

    stepVars = satCounter - 1;
    Logger.log(Logger.INFO, "Number of SAT variables: " + stepVars);
  }

  protected void setPredicateIDs() {
    predicates = new HashMap<>();
    predicateSatId = new ArrayList<>();
    preconditionsPos = new ArrayList<>();
    preconditionsNeg = new ArrayList<>();
    effectsPos = new ArrayList<>();
    effectsNeg = new ArrayList<>();
    for (Condition p : graph.getLiftedState(graph.getCurrentLayer())) {
      System.out.println(p);
      predicates.put(p, predicates.size());
      predicateSatId.add(satCounter++);
      preconditionsPos.add(new HashSet<>());
      preconditionsNeg.add(new HashSet<>());
      effectsPos.add(new HashSet<>());
      effectsNeg.add(new HashSet<>());
    }
  }

  protected void setOperatorIDs() {
    operators = new HashMap<>();
    operatorSatId = new ArrayList<>();
    parameterSatId = new ArrayList<>();
    eligibleArguments = new ArrayList<>();
    Map<String, Operator> operatorLookup = new HashMap<>();
    Logger.log(Logger.INFO, "Number of lifted operators: " + problem.getOperators().size());
    problem.getOperators().forEach(o -> operatorLookup.put(o.getName(), o));
    for (Operator groundedOperator : graph.getLiftedActions()) {
      Operator liftedOperator = operatorLookup.get(groundedOperator.getName());
      int numParameters = groundedOperator.getArguments().size();
      List<Argument> groundedArgs = new ArrayList<>();
      // operator.getArguments().forEach(arg -> {
      // if (isGrounded.test(operator, arg)) {
      // groundedArgs.add(arg);
      // } else {
      // groundedArgs.add(null);
      // }
      // });
      for (int i = 0; i < numParameters; i++) {
        if (isGrounded.test(liftedOperator, liftedOperator.getArguments().get(i))) {
          groundedArgs.add(groundedOperator.getArguments().get(i));
        } else {
          groundedArgs.add(null);
        }
      }
      Operator newOperator = liftedOperator.getOperatorWithGroundArguments(groundedArgs);
      Integer operatorId = operators.get(newOperator);
      if (operatorId == null) {
        operatorId = operators.size();
        System.out.println("New operator " + operatorId + ": " + newOperator);
        operators.put(newOperator, operatorId);
        operatorSatId.add(satCounter++);
        List<Map<Argument, Integer>> operatorArguments = new ArrayList<>();
        List<List<Integer>> satId = new ArrayList<>();
        for (int i = 0; i < numParameters; i++) {
          if (newOperator.getArguments().get(i).isConstant()) {
            satId.add(null);
            operatorArguments.add(null);
          } else {
            satId.add(new ArrayList<>());
            operatorArguments.add(new HashMap<>());
          }
        }
        parameterSatId.add(satId);
        eligibleArguments.add(operatorArguments);
      }
      for (int i = 0; i < numParameters; i++) {
        if (newOperator.getArguments().get(i).isConstant()) {
          continue;
        }
        Map<Argument, Integer> knownArguments = eligibleArguments.get(operatorId).get(i);
        Argument argument = groundedOperator.getArguments().get(i);
        if (!knownArguments.containsKey(argument)) {
          System.out.println("New argument for " + operatorId + " at pos " + i + ": " + argument);
          knownArguments.put(argument, knownArguments.size());
          parameterSatId.get(operatorId).get(i).add(satCounter++);
        }
      }
      for (boolean isPrecondition : Arrays.asList(true, false)) {
        Pair<ConditionSet, ConditionSet> split = isPrecondition ? grounder.splitCondition(newOperator.getPrecondition())
            : grounder.splitCondition(newOperator.getEffect());
        ConditionSet simpleSet = split.getLeft();
        if (split.getRight() != null) {
          if (split.getRight().getConditions().size() > 0) {
            Logger.log(Logger.ERROR, "Precondition contains complex set: " + split);
            System.exit(1);
          }
        }
        for (AbstractCondition c : simpleSet.getConditions()) {
          if (c.getConditionType() != ConditionType.atomic) {
            Logger.log(Logger.ERROR, "A simple set of conditions contains non-atomic condition " + c + ".");
            System.exit(1);
          }
          Condition condition = (Condition) c;
          ParameterMatching matching = getParameterMatching(newOperator, condition);
          Condition groundCondition = condition.getConditionBoundToArguments(newOperator.getArguments(),
              groundedOperator.getArguments());
          List<Integer> position = new ArrayList<>();
          List<Integer> argumentId = new ArrayList<>();
          // System.out.println("for operator " + newOperator);
          // System.out.println("Arguments: " + eligibleArguments.get(operatorId));
          // System.out.println("Predicate: " + precondition);
          // System.out.println("GroundPredicate: " + groundPrecondition);
          for (int i = 0; i < matching.size(); i++) {
            position.add(matching.getOperatorPos(i));
            argumentId.add(matching.getArgumentId(groundCondition, i));
          }
          // System.out.println("Positions: " + position);
          // System.out.println("Ids: " + argumentId);
          if (groundCondition.isNegated()) {
            if (isPrecondition) {
              preconditionsNeg.get(predicates.get(groundCondition.withoutNegation()))
                  .add(new Assignment(operatorId, position, argumentId));
            } else {
              effectsNeg.get(predicates.get(groundCondition.withoutNegation()))
                  .add(new Assignment(operatorId, position, argumentId));
            }
          } else {
            if (isPrecondition) {
              preconditionsPos.get(predicates.get(groundCondition))
                  .add(new Assignment(operatorId, position, argumentId));
            } else {
              effectsPos.get(predicates.get(groundCondition)).add(new Assignment(operatorId, position, argumentId));
            }
          }
        }
      }
    }
    System.out.println("Preconditions: " + preconditionsPos);
    System.out.println("");
    System.out.println(preconditionsNeg);
    System.out.println("Effects: " + effectsPos);
    System.out.println("");
    System.out.println(effectsNeg);
  }

  protected void setForbiddenConditions(Operator o, Condition c) {
    ParameterMatching matching = getParameterMatching(o, c);
    List<Argument> variableParameters = new ArrayList<>();
    List<List<Argument>> eligible = new ArrayList<>();
    for (int i = 0; i < matching.size(); i++) {
      variableParameters.add(c.getArguments().get(matching.getPredicatePos(i)));
      eligible.add(
          new ArrayList<>(eligibleArguments.get(matching.getOperatorId()).get(matching.getOperatorPos(i)).keySet()));
    }
    ArgumentCombinationUtils.iterator(eligible).forEachRemaining(args -> {
      Condition groundCondition = c.getConditionBoundToArguments(variableParameters, args);
      if (!predicates.containsKey(groundCondition.withoutNegation())) {
        System.out.println("Forbidden for operator " + operators.get(o) + ": " + args);
        List<Integer> position = new ArrayList<>();
        List<Integer> argumentId = new ArrayList<>();
        for (int i = 0; i < matching.size(); i++) {
          position.add(matching.getOperatorPos(i));
          argumentId.add(matching.getArgumentId(groundCondition, i));
        }
        forbidden.add(new Assignment(matching.getOperatorId(), position, argumentId));
      }
    });
  }

  protected void generateClauses() {
    universalClauses = new ArrayList<>();
    transitionClauses = new ArrayList<>();
    setInitialState();
    addParameterClauses();
    addConditionClauses();
    addInterferenceClauses();
    addFrameAxioms();
    addForbiddenClauses();
    setGoal();
    Logger.log(Logger.INFO, "Number of SAT clauses: " + universalClauses.size() + transitionClauses.size());
  }

  protected void setInitialState() {
    initialClauses = new ArrayList<>();
    for (Condition c : predicates.keySet()) {
      if (problem.getInitialState().contains(c)) {
        initialClauses.add(new int[] { getPredicateSatId(predicates.get(c), false) });
      } else {
        initialClauses.add(new int[] { -getPredicateSatId(predicates.get(c), false) });
      }
    }
    // System.out.println("Initial state: " + initialClauses);
  }

  protected void addParameterClauses() {
    for (int oId : operators.values()) {
      for (int pos = 0; pos < eligibleArguments.get(oId).size(); pos++) {
        Map<Argument, Integer> arguments = eligibleArguments.get(oId).get(pos);
        if (arguments == null) {
          continue;
        }
        int numArgs = arguments.size();
        {
          // Operator -> each parameter
          int[] clause = new int[numArgs + 1];
          int counter = 0;
          clause[counter++] = -getOperatorSatId(oId);
          for (int aId : arguments.values()) {
            clause[counter++] = getParameterSatId(oId, pos, aId);
          }
          System.out.print("Operator " + oId + " Param " + pos + ": [ ");
          for (int i : clause) {
            System.out.print(i + " ");
          }
          System.out.println("]");
          universalClauses.add(clause);
        }
        // {
        // // Parameter -> Operator
        // for (int aId : arguments.values()) {
        // int[] clause = new int[2];
        // clause[0] = -getParameterSatId(oId, pos, aId);
        // clause[1] = getOperatorSatId(oId);
        // universalClauses.add(clause);
        // }
        // }
        {
          // <=1 per Parameter
          for (int aId1 : arguments.values()) {
            for (int aId2 : arguments.values()) {
              if (aId1 >= aId2) {
                continue;
              }
              int[] clause = new int[2];
              clause[0] = -getParameterSatId(oId, pos, aId1);
              clause[1] = -getParameterSatId(oId, pos, aId2);
              universalClauses.add(clause);
            }
          }
        }
      }
    }
  }

  protected void addConditionClauses() {
    for (int pId : predicates.values()) {
      for (boolean isPrecondition : Arrays.asList(true, false)) {
        for (boolean isPositive : Arrays.asList(true, false)) {
          // System.out.println("Condition: " + c);
          Set<Assignment> support;
          if (isPrecondition) {
            if (isPositive) {
              support = preconditionsPos.get(pId);
            } else {
              support = preconditionsNeg.get(pId);
            }
          } else {
            if (isPositive) {
              support = effectsPos.get(pId);
            } else {
              support = effectsNeg.get(pId);
            }
          }
          for (Assignment assignment : support) {
            int oId = assignment.getOperatorId();
            // System.out.println("Operator: " + oNr);
            int[] clause = new int[assignment.size() + 2];
            int counter = 0;
            clause[counter++] = -getOperatorSatId(oId);
            for (int i = 0; i < assignment.size(); i++) {
              clause[counter++] = -getParameterSatId(oId, assignment.getPosition(i), assignment.getArgumentId(i));
            }
            clause[counter++] = (isPositive ? 1 : -1) * getPredicateSatId(pId, !isPrecondition);
            System.out.print("Operator " + oId + " supports " + pId + ": [ ");
            for (int i : clause) {
              System.out.print(i + " ");
            }
            System.out.println("]");
            if (isPrecondition) {
              universalClauses.add(clause);
            } else {
              transitionClauses.add(clause);
            }
          }
        }
      }
    }
  }

  protected void addInterferenceClauses() {
    for (int pId : predicates.values()) {
      for (boolean isPositive : Arrays.asList(true, false)) {
        Set<Assignment> effectSupport;
        Set<Assignment> precondSupport;
        if (isPositive) {
          effectSupport = effectsPos.get(pId);
          precondSupport = preconditionsNeg.get(pId);
        } else {
          effectSupport = effectsNeg.get(pId);
          precondSupport = preconditionsPos.get(pId);
        }
        for (Assignment effectAssignment : effectSupport) {
          int effectOperatorId = effectAssignment.getOperatorId();
          for (Assignment precondAssignment : precondSupport) {
            int precondOperatorId = precondAssignment.getOperatorId();
            if (effectOperatorId == precondOperatorId) {
              continue;
            }
            int[] clause = new int[effectAssignment.size() + precondAssignment.size() + 2];
            int counter = 0;
            clause[counter++] = -getOperatorSatId(effectOperatorId);
            clause[counter++] = -getOperatorSatId(precondOperatorId);
            for (int i = 0; i < effectAssignment.size(); i++) {
              clause[counter++] = -getParameterSatId(effectOperatorId, effectAssignment.getPosition(i),
                  effectAssignment.getArgumentId(i));
            }
            for (int i = 0; i < precondAssignment.size(); i++) {
              clause[counter++] = -getParameterSatId(precondOperatorId, precondAssignment.getPosition(i),
                  precondAssignment.getArgumentId(i));
            }
            System.out.print(
                "Operator " + effectOperatorId + " interferes with " + precondOperatorId + " on " + pId + ": [ ");
            for (int i : clause) {
              System.out.print(i + " ");
            }
            System.out.println("]");
            universalClauses.add(clause);
          }
        }
      }
    }
  }

  protected void addFrameAxioms() {
    for (int pId : predicates.values()) {
      for (boolean isPositive : Arrays.asList(true, false)) {
        Set<Assignment> support;
        if (isPositive) {
          support = effectsPos.get(pId);
        } else {
          support = effectsNeg.get(pId);
        }
        List<int[]> dnf = new ArrayList<>();
        dnf.add(new int[] { (isPositive ? 1 : -1) * getPredicateSatId(pId, false) });
        dnf.add(new int[] { (isPositive ? -1 : 1) * getPredicateSatId(pId, true) });
        for (Assignment assignment : support) {
          int[] clause = new int[assignment.size() + 1];
          int counter = 0;
          clause[counter++] = getOperatorSatId(assignment.getOperatorId());
          for (int i = 0; i < assignment.size(); i++) {
            clause[counter++] = getParameterSatId(assignment.getOperatorId(), assignment.getPosition(i),
                assignment.getArgumentId(i));
          }
          System.out
              .print("Predicate " + pId + " has support from " + assignment.getOperatorId() + ": [ ");
          for (int i : clause) {
            System.out.print(i + " ");
          }
          System.out.println("]");
          dnf.add(clause);
        }
        // System.out.println("DNF: " + dnf);
        // System.out.println("CNF: " + DNF2CNF(dnf));
        transitionClauses.addAll(DNF2CNF(dnf));
      }
    }
  }

  protected void addForbiddenClauses() {
    for (Assignment assignment : forbidden) {
      int oNr = assignment.getOperatorId();
      int[] clause = new int[assignment.size()];
      int counter = 0;
      for (int i = 0; i < assignment.size(); i++) {
        clause[counter++] = -getParameterSatId(oNr, assignment.getPosition(i), assignment.getArgumentId(i));
      }
      universalClauses.add(clause);
    }
  }

  protected void setGoal() {
    ConditionSet goalSet = new ConditionSet(ConditionType.conjunction);
    problem.getGoals().forEach(c -> goalSet.add(c));
    Pair<ConditionSet, ConditionSet> split = grounder.splitCondition(goalSet);
    ConditionSet simpleSet = split.getLeft();
    if (split.getRight() != null) {
      if (split.getRight().getConditions().size() > 0) {
        Logger.log(Logger.ERROR, "Goal contains complex set: " + split);
        System.exit(1);
      }
    }
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

  protected int satCounter;
  protected BiPredicate<Operator, Argument> isGrounded;
}
