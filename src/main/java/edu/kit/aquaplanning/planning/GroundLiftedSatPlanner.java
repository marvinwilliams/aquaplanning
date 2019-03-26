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
    isGrounded = (o, a) -> a.getName().startsWith("?h") && false;
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
    for (Condition p : graph.getLiftedState(graph.getCurrentLayer())) {
      // System.out.println(p);
      predicates.put(p, predicates.size());
      predicateSatId.add(satCounter++);
      preconditionsPos.add(new HashSet<>());
      preconditionsNeg.add(new HashSet<>());
      effectsPos.add(new HashSet<>());
      effectsNeg.add(new HashSet<>());
    }
    Logger.log(Logger.INFO, "Number of predicates: " + graph.getLiftedState(graph.getCurrentLayer()).size());
  }

  protected void setOperators() {
    operators = new HashMap<>();
    operatorSatId = new ArrayList<>();
    parameterSatId = new ArrayList<>();
    eligibleArguments = new ArrayList<>();
    Map<String, Operator> operatorLookup = new HashMap<>();
    Logger.log(Logger.INFO, "Number of lifted operators: " + problem.getOperators().size());
    problem.getOperators().forEach(o -> operatorLookup.put(o.getName(), o));
    for (Operator operator : graph.getLiftedActions()) {
      Operator liftedOperator = operatorLookup.get(operator.getName());
      int numParameters = operator.getArguments().size();
      List<Argument> groundedArgs = new ArrayList<>();
      operator.getArguments().forEach(arg -> {
        if (isGrounded.test(operator, arg)) {
          groundedArgs.add(arg);
        } else {
          groundedArgs.add(null);
        }
      });
      Operator newOperator = liftedOperator.getOperatorWithGroundArguments(groundedArgs);
      Integer operatorId = operators.get(newOperator);
      if (operatorId == null) {
        operatorId = operators.size();
        // System.out.println("New operator " + operatorId + ": " + newOperator);
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
        Map<Argument, Integer> knownArguments = eligibleArguments.get(operatorId).get(i);
        if (knownArguments == null) {
          continue;
        }
        Argument argument = operator.getArguments().get(i);
        if (!knownArguments.containsKey(argument)) {
          // System.out.println("New argument at pos " + i + ": " + argument);
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
              operator.getArguments());
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
    // System.out.println("Preconditions: " + preconditionsPos);
    // System.out.println("");
    // System.out.println(preconditionsNeg);
    // System.out.println("Effects: " + effectsPos);
    // System.out.println("");
    // System.out.println(effectsNeg);
  }

  protected void initIDs() {
    satCounter = 1;

    setPredicates();

    Logger.log(Logger.INFO, "Number of predicates: " + predicates.size());

    setOperators();

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
          addForbiddenConditions(operator, condition);
        }
      }
    }
    Logger.log(Logger.INFO, "Number of operators: " + operators.size());

    stepVars = satCounter - 1;
    Logger.log(Logger.INFO, "Number of SAT variables: " + stepVars);
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
    for (Condition c : predicates.keySet()) {
      if (problem.getInitialState().contains(c)) {
        initialClauses.add(new int[] { getPredicateSatId(predicates.get(c), false) });
      } else {
        initialClauses.add(new int[] { -getPredicateSatId(predicates.get(c), false) });
      }
    }
    // System.out.println("Initial state: " + initialClauses);
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
        // System.out.println("Forbidden for operator " + operators.get(o) + ": " + args);
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

  protected List<int[]> DNF2CNF(List<int[]> dnf) {
    List<int[]> result = new ArrayList<>();
    DNF2CNF(dnf, 0, result, new int[dnf.size()]);
    return result;
  }

  protected void DNF2CNF(List<int[]> dnf, int depth, List<int[]> result, int[] current) {
    if (depth == dnf.size()) {
      result.add(current);
    } else {
      for (int i : dnf.get(depth)) {
        int[] tmp = current.clone();
        tmp[depth] = i;
        DNF2CNF(dnf, depth + 1, result, tmp);
      }
    }
  }

  protected PlanningProblem problem;
  protected RelaxedPlanningGraph graph;
  protected RelaxedPlanningGraphGrounder grounder;

  protected Map<Condition, Integer> predicates;
  protected Map<Operator, Integer> operators;
  protected List<List<Map<Argument, Integer>>> eligibleArguments;

  protected List<Set<Assignment>> preconditionsPos;
  protected List<Set<Assignment>> preconditionsNeg;
  protected List<Set<Assignment>> effectsPos;
  protected List<Set<Assignment>> effectsNeg;
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
