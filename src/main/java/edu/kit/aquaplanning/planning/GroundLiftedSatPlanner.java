package edu.kit.aquaplanning.planning;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiPredicate;
import java.util.stream.Collectors;

import edu.kit.aquaplanning.Configuration;
import edu.kit.aquaplanning.grounding.ArgumentCombinationUtils;
import edu.kit.aquaplanning.grounding.RelaxedPlanningGraph;
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
    isGrounded = (o, a) -> a.getName().startsWith("?x") && false;
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
    // Decode the plan
    Plan plan = new Plan();
    grounder.ground(problem);
    int[] model = solver.getModel();
    for (int s = 0; s < step; s++) {
      for (Operator o : operators.keySet()) {
        int i = operators.get(o);
        if (model[getOperatorSatId(i) + s * stepVars] > 0) {
          List<Argument> args = new ArrayList<>();
          for (int j = 0; j < o.getArguments().size(); j++) {
            if (o.getArguments().get(j).isConstant()) {
              args.add(null);
              continue;
            }
            boolean found = eligibleArguments.get(i).get(j).size() == 0;
            for (Argument arg : eligibleArguments.get(i).get(j).keySet()) {
              int k = eligibleArguments.get(i).get(j).get(arg);
              if (model[getParameterSatId(i, j, k) + s * stepVars] >= 0) {
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

  protected void setPredicates() {
    predicates = new HashMap<>();
    predicateSatId = new ArrayList<>();
    preconditionsPos = new ArrayList<>();
    preconditionsNeg = new ArrayList<>();
    effectsPos = new ArrayList<>();
    effectsNeg = new ArrayList<>();
    Logger.log(Logger.INFO, "Number of predicates: " + graph.getLiftedState(graph.getCurrentLayer()).size());
    for (Condition p : graph.getLiftedState(graph.getCurrentLayer())) {
      predicates.put(p, predicates.size());
      predicateSatId.add(satCounter++);
      preconditionsPos.add(new HashSet<>());
      preconditionsNeg.add(new HashSet<>());
      effectsPos.add(new HashSet<>());
      effectsNeg.add(new HashSet<>());
    }
  }

  protected void setOperators() {
    operators = new HashMap<>();
    operatorSatId = new ArrayList<>();
    parameterSatId = new ArrayList<>();
    eligibleArguments = new ArrayList<>();
    Map<String, Operator> operatorLookup = new HashMap<>();
    Logger.log(Logger.INFO, "Number of lifted operators: " + problem.getOperators().size());
    for (Operator operator : problem.getOperators()) {
      operatorLookup.put(operator.getName(), operator);
    }
    for (Operator operator : graph.getLiftedActions()) {
      Operator liftedOperator = operatorLookup.get(operator.getName());
      List<Argument> groundedArgs = new ArrayList<>();
      for (Argument a : operator.getArguments()) {
        if (isGrounded.test(operator, a)) {
          groundedArgs.add(a);
        } else {
          groundedArgs.add(null);
        }
      }
      Operator newOperator = liftedOperator.getOperatorWithGroundArguments(groundedArgs);
      Integer operatorId = operators.get(newOperator);
      if (operatorId == null) {
        operatorId = operators.size();
        // System.out.println("New operator " + operatorId + ": " + newOperator);
        operators.put(newOperator, operatorId);
        operatorSatId.add(satCounter++);
        List<Map<Argument, Integer>> operatorArguments = new ArrayList<>();
        List<List<Integer>> satId = new ArrayList<>();
        for (int i = 0; i < newOperator.getArguments().size(); i++) {
          satId.add(new ArrayList<>());
          operatorArguments.add(new HashMap<>());
        }
        parameterSatId.add(satId);
        eligibleArguments.add(operatorArguments);
      }
      for (int i = 0; i < newOperator.getArguments().size(); i++) {
        if (!newOperator.getArguments().get(i).isConstant()) {
          if (eligibleArguments.get(operatorId).get(i).putIfAbsent(operator.getArguments().get(i),
              eligibleArguments.get(operatorId).get(i).size()) == null) {
            parameterSatId.get(operatorId).get(i).add(satCounter++);
          }
        }
      }
      {
        Pair<ConditionSet, ConditionSet> split = grounder.splitCondition(newOperator.getPrecondition());
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
          Condition precondition = (Condition) c;
          ParameterMatching matching = getParameterMatching(newOperator, precondition);
          Condition groundPrecondition = precondition.getConditionBoundToArguments(newOperator.getArguments(),
              operator.getArguments());
          List<Integer> position = new ArrayList<>();
          List<Integer> argumentId = new ArrayList<>();
          // System.out.println("for operator " + newOperator);
          // System.out.println("Arguments: " + eligibleArguments.get(operatorId));
          // System.out.println("Predicate: " + precondition);
          // System.out.println("GroundPredicate: " + groundPrecondition);
          for (int i = 0; i < matching.size(); i++) {
            position.add(matching.getOperatorPos(i));
            argumentId.add(matching.getArgumentId(groundPrecondition, i));
          }
          // System.out.println("Positions: " + position);
          // System.out.println("Ids: " + argumentId);
          if (groundPrecondition.isNegated()) {
            preconditionsNeg.get(predicates.get(groundPrecondition.withoutNegation()))
                .add(new Assignment(operatorId, position, argumentId));
          } else {
            preconditionsPos.get(predicates.get(groundPrecondition))
                .add(new Assignment(operatorId, position, argumentId));
          }
        }
      }
      {
        Pair<ConditionSet, ConditionSet> split = grounder.splitCondition(newOperator.getEffect());
        ConditionSet simpleSet = split.getLeft();
        if (split.getRight() != null) {
          if (split.getRight().getConditions().size() > 0) {
            Logger.log(Logger.ERROR, "Effect contains complex set: " + split);
            System.exit(1);
          }
        }
        for (AbstractCondition c : simpleSet.getConditions()) {
          if (c.getConditionType() != ConditionType.atomic) {
            Logger.log(Logger.ERROR, "A simple set of conditions contains non-atomic condition " + c + ".");
            System.exit(1);
          }
          Condition effect = (Condition) c;
          ParameterMatching matching = getParameterMatching(newOperator, effect);
          Condition groundEffect = effect.getConditionBoundToArguments(newOperator.getArguments(),
              operator.getArguments());
          List<Integer> position = new ArrayList<>();
          List<Integer> argumentId = new ArrayList<>();
          for (int i = 0; i < matching.size(); i++) {
            position.add(matching.getOperatorPos(i));
            argumentId.add(matching.getArgumentId(groundEffect, i));
          }
          if (groundEffect.isNegated()) {
            effectsNeg.get(predicates.get(groundEffect.withoutNegation()))
                .add(new Assignment(operatorId, position, argumentId));
          } else {
            effectsPos.get(predicates.get(groundEffect)).add(new Assignment(operatorId, position, argumentId));
          }
        }
      }
    }
    System.out.println("Positive preconditions: " + preconditionsPos);
  }

  protected void initIDs() {
    satCounter = 1;

    setPredicates();

    Logger.log(Logger.INFO, "Number of predicates: " + predicates.size());

    setOperators();

    forbidden = new HashSet<>();
    for (Operator operator : operators.keySet()) {
      {
        ConditionSet simpleSet = grounder.splitCondition(operator.getPrecondition()).getLeft();
        for (AbstractCondition c : simpleSet.getConditions()) {
          if (c.getConditionType() != ConditionType.atomic) {
            Logger.log(Logger.ERROR, "A simple set of conditions contains non-atomic condition " + c + ".");
            System.exit(1);
          }
          Condition precondition = (Condition) c;
          addForbiddenConditions(operator, precondition);
        }
      }
      {
        ConditionSet simpleSet = grounder.splitCondition(operator.getEffect()).getLeft();
        for (AbstractCondition c : simpleSet.getConditions()) {
          if (c.getConditionType() != ConditionType.atomic) {
            Logger.log(Logger.ERROR, "A simple set of conditions contains non-atomic condition " + c + ".");
            System.exit(1);
          }
          Condition effect = (Condition) c;
          addForbiddenConditions(operator, effect);
        }
      }
    }
    Logger.log(Logger.INFO, "Number of operators: " + operators.size());

    stepVars = satCounter - 1;
    Logger.log(Logger.INFO, "Number of SAT variables: " + stepVars);
  }

  protected void addParameterClauses() {
    for (Operator operator : operators.keySet()) {
      int oNr = operators.get(operator);
      for (int pos = 0; pos < eligibleArguments.get(oNr).size(); pos++) {
        Argument argument = operator.getArguments().get(pos);
        if (argument.isConstant()) {
          continue;
        }
        int numArgs = eligibleArguments.get(oNr).get(pos).size();
        {
          // Operator -> each parameter
          int[] clause = new int[numArgs + 1];
          clause[0] = -getOperatorSatId(oNr);
          for (int i = 0; i < numArgs; i++) {
            clause[i + 1] = getParameterSatId(oNr, pos, i);
          }
          universalClauses.add(clause);
        }
        {
          // Parameter -> Operator
          for (int i = 0; i < numArgs; i++) {
            int[] clause = new int[2];
            clause[0] = -getParameterSatId(oNr, pos, i);
            clause[1] = getOperatorSatId(oNr);
            universalClauses.add(clause);
          }
        }
        {
          // <=1 per Parameter
          for (int c1 = 0; c1 < numArgs; c1++) {
            for (int c2 = c1 + 1; c2 < numArgs; c2++) {
              int[] clause = new int[2];
              clause[0] = -getParameterSatId(oNr, pos, c1);
              clause[1] = -getParameterSatId(oNr, pos, c2);
              universalClauses.add(clause);
            }
          }
        }
      }
    }
  }

  protected void addConditionClauses(List<Set<Assignment>> conditionSupport, boolean positive, boolean nextStep) {
    for (Condition c : predicates.keySet()) {
      // System.out.println("Condition: " + c);
      int pNr = predicates.get(c);
      for (Assignment assignment : conditionSupport.get(pNr)) {
        int oNr = assignment.getOperatorId();
        // System.out.println("Operator: " + oNr);
        int[] clause = new int[assignment.size() + 1];
        for (int i = 0; i < assignment.size(); i++) {
          clause[i] = -getParameterSatId(oNr, assignment.getPosition(i), assignment.getArgumentId(i));
        }
        clause[assignment.size()] = (positive ? 1 : -1) * getPredicateSatId(pNr, nextStep);
        if (nextStep) {
          transitionClauses.add(clause);
        } else {
          universalClauses.add(clause);
        }
      }
    }
  }

  protected void addInterferenceClauses() {
    for (Condition c : predicates.keySet()) {
      int pNr = predicates.get(c);
      for (Assignment effectAssignment : effectsPos.get(pNr)) {
        int effectOperatorId = effectAssignment.getOperatorId();
        for (Assignment precondAssignment : preconditionsNeg.get(pNr)) {
          int precondOperatorId = precondAssignment.getOperatorId();
          if (effectOperatorId == precondOperatorId) {
            continue;
          }
          int[] clause = new int[effectAssignment.size() + precondAssignment.size()];
          int counter = 0;
          for (int i = 0; i < effectAssignment.size(); i++) {
            clause[counter++] = -getParameterSatId(effectOperatorId, effectAssignment.getPosition(i),
                effectAssignment.getArgumentId(i));
          }
          for (int i = 0; i < precondAssignment.size(); i++) {
            clause[counter++] = -getParameterSatId(precondOperatorId, precondAssignment.getPosition(i),
                precondAssignment.getArgumentId(i));
          }
          universalClauses.add(clause);
        }
      }
      for (Assignment effectAssignment : effectsNeg.get(pNr)) {
        int effectOperatorId = effectAssignment.getOperatorId();
        for (Assignment precondAssignment : preconditionsPos.get(pNr)) {
          int precondOperatorId = precondAssignment.getOperatorId();
          if (effectOperatorId == precondOperatorId) {
            continue;
          }
          int[] clause = new int[effectAssignment.size() + precondAssignment.size()];
          int counter = 0;
          for (int i = 0; i < effectAssignment.size(); i++) {
            clause[counter++] = -getParameterSatId(effectOperatorId, effectAssignment.getPosition(i),
                effectAssignment.getArgumentId(i));
          }
          for (int i = 0; i < precondAssignment.size(); i++) {
            clause[counter++] = -getParameterSatId(precondOperatorId, precondAssignment.getPosition(i),
                precondAssignment.getArgumentId(i));
          }
          universalClauses.add(clause);
        }
      }
    }
  }

  protected void addFrameAxioms() {
    class SingleAssignment {
      int operatorId;
      int position;
      int argumentId;

      SingleAssignment(int operatorId, int position, int argumentId) {
        this.operatorId = operatorId;
        this.position = position;
        this.argumentId = argumentId;
      }

      @Override
      public String toString() {
        return "[" + operatorId + "| " + position + ":" + argumentId + "]";
      }
    }
    for (int pNr = 0; pNr < predicates.size(); pNr++) {
      int copy = pNr;
      {
        List<List<SingleAssignment>> combinedArguments = new ArrayList<>();
        for (Assignment assignment : effectsPos.get(pNr)) {
          for (int i = 0; i < assignment.size(); i++) {
            if (i >= combinedArguments.size()) {
              combinedArguments.add(new ArrayList<>());
            }
            combinedArguments.get(i).add(new SingleAssignment(assignment.getOperatorId(), assignment.getPosition(i),
                assignment.getArgumentId(i)));
          }
        }
        System.out.println("CombinedArguments: " + combinedArguments);
        ArgumentCombinationUtils.iterator(combinedArguments).forEachRemaining(args -> {
          System.out.println(args);
          int[] clause = new int[2 + args.size()];
          clause[0] = getPredicateSatId(copy, false);
          clause[1] = -getPredicateSatId(copy, true);
          int counter = 2;
          for (SingleAssignment arg : args) {
            clause[counter++] = getParameterSatId(arg.operatorId, arg.position, arg.argumentId);
          }
          transitionClauses.add(clause);
        });
      }
      {
        List<List<SingleAssignment>> combinedArguments = new ArrayList<>();
        for (Assignment assignment : effectsNeg.get(pNr)) {
          for (int i = 0; i < assignment.size(); i++) {
            if (i >= combinedArguments.size()) {
              combinedArguments.add(new ArrayList<>());
            }
            combinedArguments.get(i).add(new SingleAssignment(assignment.getOperatorId(), assignment.getPosition(i),
                assignment.getArgumentId(i)));
          }
        }
        ArgumentCombinationUtils.iterator(combinedArguments).forEachRemaining(args -> {
          int[] clause = new int[2 + args.size()];
          clause[0] = -getPredicateSatId(copy, false);
          clause[1] = getPredicateSatId(copy, true);
          int counter = 2;
          for (SingleAssignment arg : args) {
            clause[counter++] = getParameterSatId(arg.operatorId, arg.position, arg.argumentId);
          }
          transitionClauses.add(clause);
        });
      }
    }
  }

  protected void addForbiddenClauses() {
    for (Assignment assignment : forbidden) {
      int oNr = assignment.getOperatorId();
      int[] clause = new int[assignment.size()];
      for (int i = 0; i < assignment.size(); i++) {
        clause[i] = -getParameterSatId(oNr, assignment.getPosition(i), assignment.getArgumentId(i));
      }
      universalClauses.add(clause);
    }
  }

  protected void generateClauses() {
    universalClauses = new ArrayList<>();
    transitionClauses = new ArrayList<>();
    setInitialState();
    setGoal();
    addParameterClauses();
    addConditionClauses(preconditionsPos, true, false);
    addConditionClauses(preconditionsNeg, false, false);
    addConditionClauses(effectsPos, true, true);
    addConditionClauses(effectsNeg, false, true);
    addInterferenceClauses();
    addFrameAxioms();
    addForbiddenClauses();
    Logger.log(Logger.INFO, "Number of SAT clauses: " + universalClauses.size() + transitionClauses.size());
  }

  protected int getPredicateSatId(int pNr, boolean nextStep) {
    return predicateSatId.get(pNr) + (nextStep ? stepVars : 0);
  }

  protected int getOperatorSatId(int oNr) {
    return operatorSatId.get(oNr);
  }

  protected int getParameterSatId(int oNr, int pos, int cNr) {
    return parameterSatId.get(oNr).get(pos).get(cNr);
  }

  protected void setInitialState() {
    initialClauses = new ArrayList<>();
    Set<Integer> allInitial = new HashSet<Integer>();
    allInitial.addAll(problem.getInitialState().stream().map(c -> predicates.get(c)).collect(Collectors.toSet()));
    for (int i = 0; i < predicates.size(); i++) {
      if (allInitial.contains(i)) {
        initialClauses.add(new int[] { getPredicateSatId(i, false) });
      } else {
        initialClauses.add(new int[] { -getPredicateSatId(i, false) });
      }
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
  }

  protected void nextStep() {
    for (int[] clause : universalClauses) {
      for (int i = 0; i < clause.length; i++) {
        if (clause[i] > 0) {
          clause[i] += stepVars;
        } else {
          clause[i] -= stepVars;
        }
      }
    }
    for (int[] clause : transitionClauses) {
      for (int i = 0; i < clause.length; i++) {
        if (clause[i] > 0) {
          clause[i] += stepVars;
        } else {
          clause[i] -= stepVars;
        }
      }
    }
    for (int i = 0; i < goalClause.length; i++) {
      if (goalClause[i] > 0) {
        goalClause[i] += stepVars;
      } else {
        goalClause[i] -= stepVars;
      }
    }
  }

  public ParameterMatching getParameterMatching(Operator o, Condition c) {
    int operatorId = operators.get(o);
    List<Integer> predicatePos = new ArrayList<>();
    List<Integer> operatorPos = new ArrayList<>();
    for (int i = 0; i < c.getArguments().size(); i++) {
      Argument a = c.getArguments().get(i);
      if (!a.isConstant()) {
        predicatePos.add(i);
        operatorPos.add(o.getArguments().indexOf(a));
      }
    }
    return new ParameterMatching(operatorId, predicatePos, operatorPos);
  }

  public void addForbiddenConditions(Operator o, Condition c) {
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

  class ParameterMatching {
    int operatorId;
    List<Integer> predicatePos;
    List<Integer> operatorPos;

    public ParameterMatching(int operatorId, List<Integer> predicatePos, List<Integer> operatorPos) {
      this.operatorId = operatorId;
      this.predicatePos = predicatePos;
      this.operatorPos = operatorPos;
    }

    public int size() {
      return predicatePos.size();
    }

    public int getPredicatePos(int i) {
      return predicatePos.get(i);
    }

    public int getOperatorPos(int i) {
      return operatorPos.get(i);
    }

    public int getArgumentId(Condition c, int i) {
      return eligibleArguments.get(operatorId).get(getOperatorPos(i)).get(c.getArguments().get(getPredicatePos(i)));
    }

    public int getOperatorId() {
      return operatorId;
    }
  }

  class Assignment {
    public int operatorId;
    public List<Integer> position;
    public List<Integer> argumentId;

    public Assignment(int operatorId, List<Integer> position, List<Integer> argumentId) {
      this.operatorId = operatorId;
      this.position = position;
      this.argumentId = argumentId;
    }

    public int size() {
      return position.size();
    }

    public int getOperatorId() {
      return operatorId;
    }

    public int getPosition(int i) {
      return position.get(i);
    }

    public int getArgumentId(int i) {
      return argumentId.get(i);
    }

    @Override
    public String toString() {
      return "Operator " + operatorId + ": " + position + "|" + argumentId;
    }

    @Override
    public int hashCode() {
      final int prime = 31;
      int result = 1;
      result = prime * result + operatorId;
      result = prime * result + position.hashCode();
      result = prime * result + argumentId.hashCode();
      return result;
    }

    @Override
    public boolean equals(Object other) {
      if (this == other) {
        return true;
      }
      if (other == null) {
        return false;
      }
      if (other.getClass() != getClass()) {
        return false;
      }
      Assignment tmp = (Assignment) other;
      if (operatorId != tmp.operatorId) {
        return false;
      }
      if (!position.equals(tmp.position)) {
        return false;
      }
      if (!argumentId.equals(tmp.argumentId)) {
        return false;
      }
      return true;
    }
  }

  protected PlanningProblem problem;
  protected RelaxedPlanningGraph graph;
  protected RelaxedPlanningGraphGrounder grounder;

  protected Map<Condition, Integer> predicates;
  protected Map<Operator, Integer> operators;
  // Operator -> Pos -> Constants
  protected List<List<Map<Argument, Integer>>> eligibleArguments;

  protected List<Set<Assignment>> preconditionsPos;
  protected List<Set<Assignment>> preconditionsNeg;
  protected List<Set<Assignment>> effectsPos;
  protected List<Set<Assignment>> effectsNeg;
  // List -> (Operator/(List->(pos, nr)))
  protected Set<Assignment> forbidden;

  protected List<Integer> predicateSatId;
  protected List<Integer> operatorSatId;
  protected List<List<List<Integer>>> parameterSatId;
  protected List<int[]> initialClauses;
  protected List<int[]> universalClauses;
  protected int[] goalClause;
  protected List<int[]> transitionClauses;
  protected int stepVars;
  protected int satCounter;
  protected BiPredicate<Operator, Argument> isGrounded;
}
