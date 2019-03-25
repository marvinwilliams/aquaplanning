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
            for (int k = 0; k < eligibleArguments.get(i).get(j).size(); k++) {
              if (model[getParameterSatId(i, j, k) + s * stepVars] >= 0) {
                args.add(eligibleArguments.get(i).get(j).get(k));
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
      preconditionsPos.add(new ArrayList<>());
      preconditionsNeg.add(new ArrayList<>());
      effectsPos.add(new ArrayList<>());
      effectsNeg.add(new ArrayList<>());
    }
  }

  protected void setOperators() {
    operators = new HashMap<>();
    operatorSatId = new ArrayList<>();
    parameterSatId = new ArrayList<>();
    eligibleArguments = new ArrayList<>();
    Map<String, Operator> operatorLookup = new HashMap<>();
    forbidden = new ArrayList<>();
    Logger.log(Logger.INFO, "Number of lifted operators: " + problem.getOperators().size());
    for (Operator operator : problem.getOperators()) {
      operatorLookup.put(operator.getName(), operator);
    }
    for (Operator operator : graph.getLiftedActions()) {
      Operator liftedOperator = operatorLookup.get(operator.getName());
      List<Argument> groundedArgs = new ArrayList<>();
      List<Argument> liftedArgs = new ArrayList<>();
      for (Argument a : operator.getArguments()) {
        if (isGrounded.test(operator, a)) {
          groundedArgs.add(a);
          liftedArgs.add(null);
        } else {
          groundedArgs.add(null);
          liftedArgs.add(a);
        }
      }
      Operator newOperator = liftedOperator.getOperatorWithGroundArguments(groundedArgs);
      Integer operatorId = operators.get(newOperator);
      if (operatorId == null) {
        operatorId = operators.size();
        operators.put(newOperator, operatorId);
        operatorSatId.add(satCounter++);
        List<List<Argument>> operatorArguments = new ArrayList<>();
        List<List<Integer>> satId = new ArrayList<>();
        for (int i = 0; i < newOperator.getArguments().size(); i++) {
          satId.add(new ArrayList<>());
          operatorArguments.add(new ArrayList<>());
        }
        parameterSatId.add(satId);
        eligibleArguments.add(operatorArguments);
        forbidden.add(new ForbiddenAssignment(newOperator));
      }
      for (int i = 0; i < liftedArgs.size(); i++) {
        if (liftedArgs.get(i) != null) {
          if (!eligibleArguments.get(operatorId).get(i).contains(liftedArgs.get(i))) {
            eligibleArguments.get(operatorId).get(i).add(liftedArgs.get(i));
            parameterSatId.get(operatorId).get(i).add(satCounter++);
          }
        }
      }
      {
        ConditionSet simpleSet = grounder.splitCondition(newOperator.getPrecondition()).getLeft();
        for (AbstractCondition c : simpleSet.getConditions()) {
          if (c.getConditionType() != ConditionType.atomic) {
            Logger.log(Logger.ERROR, "A simple set of conditions contains non-atomic condition " + c + ".");
            System.exit(1);
          }
          Condition precondition = (Condition) c;
          SupportAssignment support = new SupportAssignment(newOperator, precondition);
          Condition groundPrecondition = precondition.getConditionBoundToArguments(newOperator.getArguments(),
              liftedArgs);
          if (groundPrecondition.isNegated()) {
            preconditionsNeg.get(predicates.get(groundPrecondition.withoutNegation())).add(support);
          } else {
            preconditionsPos.get(predicates.get(groundPrecondition)).add(support);
          }
        }
      }
      {
        ConditionSet simpleSet = grounder.splitCondition(newOperator.getEffect()).getLeft();
        for (AbstractCondition c : simpleSet.getConditions()) {
          if (c.getConditionType() != ConditionType.atomic) {
            Logger.log(Logger.ERROR, "A simple set of conditions contains non-atomic condition " + c + ".");
            System.exit(1);
          }
          Condition precondition = (Condition) c;
          SupportAssignment support = new SupportAssignment(newOperator, precondition);
          Condition groundPrecondition = precondition.getConditionBoundToArguments(newOperator.getArguments(),
              liftedArgs);
          if (groundPrecondition.isNegated()) {
            effectsNeg.get(predicates.get(groundPrecondition.withoutNegation())).add(support);
          } else {
            effectsPos.get(predicates.get(groundPrecondition)).add(support);
          }
        }
      }
    }
  }

  protected void initIDs() {
    satCounter = 1;

    setPredicates();

    Logger.log(Logger.INFO, "Number of predicates: " + predicates.size());

    setOperators();

    for (Operator operator : operators.keySet()) {
      int operatorId = operators.get(operator);
      {
        ConditionSet simpleSet = grounder.splitCondition(operator.getPrecondition()).getLeft();
        for (AbstractCondition c : simpleSet.getConditions()) {
          if (c.getConditionType() != ConditionType.atomic) {
            Logger.log(Logger.ERROR, "A simple set of conditions contains non-atomic condition " + c + ".");
            System.exit(1);
          }
          Condition precondition = (Condition) c;
          forbidden.get(operatorId).addCondition(precondition);
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
          forbidden.get(operatorId).addCondition(effect);
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
        List<Argument> args = eligibleArguments.get(oNr).get(pos);
        {
          // Operator -> each parameter
          int[] clause = new int[args.size() + 1];
          clause[0] = -getOperatorSatId(oNr);
          for (int i = 0; i < args.size(); i++) {
            clause[i + 1] = getParameterSatId(oNr, pos, i);
          }
          universalClauses.add(clause);
        }
        {
          // <=1 per Parameter
          for (int c1 = 0; c1 < args.size(); c1++) {
            for (int c2 = c1 + 1; c2 < args.size(); c2++) {
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

  protected void addConditionClauses(List<List<SupportAssignment>> conditionSupport, boolean positive,
      boolean nextStep) {
    for (Condition c: predicates.keySet()) {
      int pNr = predicates.get(c);
      for (SupportAssignment assignment : conditionSupport.get(pNr)) {
        int oNr = operators.get(assignment.getOperator());
        int[] clause = new int[2 + assignment.size()];
        clause[0] = -getOperatorSatId(oNr);
        for (int i = 0; i < assignment.size(); i++) {
          clause[i + 1] = -getParameterSatId(oNr, assignment.getOperatorPos(i), assignment.getArgumentPos(c, i));
        }
        clause[assignment.size() + 1] = (positive ? 1 : -1) * getPredicateSatId(pNr, nextStep);
        if (nextStep) {
          transitionClauses.add(clause);
        } else {
          universalClauses.add(clause);
        }
      }
    }
  }

  protected void addInterferenceClauses() {
    for (Condition c: predicates.keySet()) {
      int pNr = predicates.get(c);
      for (SupportAssignment effectAssignment : effectsPos.get(pNr)) {
        int effectNr = operators.get(effectAssignment.getOperator());
        for (SupportAssignment precondAssignment : preconditionsNeg.get(pNr)) {
          int precondNr = operators.get(precondAssignment.getOperator());
          if (effectNr == precondNr) {
            continue;
          }
          int[] clause = new int[2 + effectAssignment.size() + precondAssignment.size()];
          clause[0] = -getOperatorSatId(effectNr);
          clause[1] = -getOperatorSatId(precondNr);
          int counter = 2;
          for (int i = 0; i < effectAssignment.size(); i++) {
            clause[counter++] = -getParameterSatId(effectNr, effectAssignment.getOperatorPos(i),
                effectAssignment.getArgumentPos(c, i));
          }
          for (int i = 0; i < precondAssignment.size(); i++) {
            clause[counter++] = -getParameterSatId(precondNr, precondAssignment.getOperatorPos(i),
                precondAssignment.getArgumentPos(c, i));
          }
          universalClauses.add(clause);
        }
      }
      for (SupportAssignment effectAssignment : effectsNeg.get(pNr)) {
        int effectNr = operators.get(effectAssignment.getOperator());
        for (SupportAssignment precondAssignment : preconditionsPos.get(pNr)) {
          int precondNr = operators.get(precondAssignment.getOperator());
          if (effectNr == precondNr) {
            continue;
          }
          int[] clause = new int[2 + effectAssignment.size() + precondAssignment.size()];
          clause[0] = -getOperatorSatId(effectNr);
          clause[1] = -getOperatorSatId(precondNr);
          int counter = 2;
          for (int i = 0; i < effectAssignment.size(); i++) {
            clause[counter++] = -getParameterSatId(effectNr, effectAssignment.getOperatorPos(i),
                effectAssignment.getArgumentPos(c, i));
          }
          for (int i = 0; i < precondAssignment.size(); i++) {
            clause[counter++] = -getParameterSatId(precondNr, precondAssignment.getOperatorPos(i),
                precondAssignment.getArgumentPos(c, i));
          }
          universalClauses.add(clause);
        }
      }
    }
  }

  protected void addFrameAxioms() {
    for (Condition c: predicates.keySet()) {
      int pNr = predicates.get(c);
      {
        List<int[]> frameAxioms = new ArrayList<>();
        frameAxioms.add(new int[2]);
        frameAxioms.get(0)[0] = getPredicateSatId(pNr, false);
        frameAxioms.get(0)[1] = -getPredicateSatId(pNr, true);
        for (SupportAssignment effectAssignment : effectsPos.get(pNr)) {
          int oNr = operators.get(effectAssignment.getOperator());
          List<int[]> newFrameAxioms = new ArrayList<>();
          for (int[] oldClause : frameAxioms) {
            {
              int[] clause = new int[oldClause.length + 1];
              System.arraycopy(oldClause, 0, clause, 0, oldClause.length);
              clause[clause.length - 1] = getOperatorSatId(oNr);
              newFrameAxioms.add(clause);
            }
            for (int i = 0; i < effectAssignment.size(); i++) {
              int[] clause = new int[oldClause.length + 1];
              System.arraycopy(oldClause, 0, clause, 0, oldClause.length);
              clause[clause.length - 1] = getParameterSatId(oNr, effectAssignment.getOperatorPos(i),
                  effectAssignment.getArgumentPos(c, i));
              newFrameAxioms.add(clause);
            }
          }
          frameAxioms = newFrameAxioms;
        }
        transitionClauses.addAll(frameAxioms);
      }
      {
        List<int[]> frameAxioms = new ArrayList<>();
        frameAxioms.add(new int[2]);
        frameAxioms.get(0)[0] = -getPredicateSatId(pNr, false);
        frameAxioms.get(0)[1] = getPredicateSatId(pNr, true);
        for (SupportAssignment effectAssignment : effectsNeg.get(pNr)) {
          int oNr = operators.get(effectAssignment.getOperator());
          List<int[]> newFrameAxioms = new ArrayList<>();
          for (int[] oldClause : frameAxioms) {
            {
              int[] clause = new int[oldClause.length + 1];
              System.arraycopy(oldClause, 0, clause, 0, oldClause.length);
              clause[clause.length - 1] = getOperatorSatId(oNr);
              newFrameAxioms.add(clause);
            }
            for (int i = 0; i < effectAssignment.size(); i++) {
              int[] clause = new int[oldClause.length + 1];
              System.arraycopy(oldClause, 0, clause, 0, oldClause.length);
              clause[clause.length - 1] = getParameterSatId(oNr, effectAssignment.getOperatorPos(i),
                  effectAssignment.getArgumentPos(c, i));
              newFrameAxioms.add(clause);
            }
          }
          frameAxioms = newFrameAxioms;
        }
        transitionClauses.addAll(frameAxioms);
      }
    }
  }

  protected void addForbiddenClauses() {
    for (ForbiddenAssignment assignment : forbidden) {
      int oNr = operators.get(assignment.getOperator());
      for (int i = 0; i < assignment.size(); i++) {
        int[] clause = new int[assignment.getPositions(i).size()];
        for (int j = 0; j < assignment.getPositions(i).size(); j++) {
          clause[j] = -getParameterSatId(oNr, assignment.getPositions(i).get(j), assignment.getArgumentPos(i).get(j));
        }
        universalClauses.add(clause);
      }
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
    ConditionSet simpleSet = grounder.splitCondition(goalSet).getLeft();
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

  class SupportAssignment {
    Operator operator;
    int operatorId;
    List<Integer> predicatePos;
    List<Integer> operatorPos;

    public SupportAssignment(Operator o, Condition c) {
      operator = o;
      operatorId = operators.get(o);
      predicatePos = new ArrayList<>();
      operatorPos = new ArrayList<>();
      for (int i = 0; i < c.getArguments().size(); i++) {
        Argument a = c.getArguments().get(i);
        if (!a.isConstant()) {
          predicatePos.add(i);
          operatorPos.add(o.getArguments().indexOf(a));
        }
      }
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

    public int getArgumentPos(Condition c, int i) {
      return eligibleArguments.get(operatorId).get(getOperatorPos(i)).indexOf(c.getArguments().get(getPredicatePos(i)));
    }

    public Operator getOperator() {
      return operator;
    }
  }

  class ForbiddenAssignment {
    Operator operator;
    int operatorId;
    List<List<Integer>> position;
    List<List<Integer>> argumentPos;

    public ForbiddenAssignment(Operator o) {
      operator = o;
      operatorId = operators.get(o);
      position = new ArrayList<>();
      argumentPos = new ArrayList<>();
    }

    public Operator getOperator() {
      return operator;
    }

    public void addCondition(Condition c) {
      SupportAssignment support = new SupportAssignment(operator, c);
      List<List<Argument>> eligible = new ArrayList<>();
      for (int i = 0; i < c.getArguments().size(); i++) {
        List<Argument> constants = new ArrayList<>();
        if (c.getArguments().get(i).isConstant()) {
          constants.add(c.getArguments().get(i));
        }
        eligible.add(constants);
      }
      for (int i = 0; i < support.size(); i++) {
        eligible.set(support.getPredicatePos(i), eligibleArguments.get(operatorId).get(support.getOperatorPos(i)));
      }
      ArgumentCombinationUtils.iterator(eligible).forEachRemaining(args -> {
        Condition groundCondition = c.getConditionBoundToArguments(c.getArguments(), args);
        if (!predicates.containsKey(groundCondition.withoutNegation())) {
          List<Integer> assignmentPos = new ArrayList<>();
          List<Integer> assignment = new ArrayList<>();
          for (int i = 0; i < support.size(); i++) {
            assignmentPos.add(support.getOperatorPos(i));
            assignment.add(eligibleArguments.get(operatorId).get(support.getOperatorPos(i))
                .indexOf(args.get(support.getPredicatePos(i))));
          }
          position.add(assignmentPos);
          argumentPos.add(assignment);
        }
      });
    }

    public int size() {
      return position.size();
    }

    public List<Integer> getPositions(int i) {
      return position.get(i);
    }

    public List<Integer> getArgumentPos(int i) {
      return argumentPos.get(i);
    }
  }

  protected PlanningProblem problem;
  protected RelaxedPlanningGraph graph;
  protected RelaxedPlanningGraphGrounder grounder;

  protected Map<Condition, Integer> predicates;
  protected Map<Operator, Integer> operators;
  // Operator -> Pos -> Constants
  protected List<List<List<Argument>>> eligibleArguments;

  protected List<List<SupportAssignment>> preconditionsPos;
  protected List<List<SupportAssignment>> preconditionsNeg;
  protected List<List<SupportAssignment>> effectsPos;
  protected List<List<SupportAssignment>> effectsNeg;
  // List -> (Operator/(List->(pos, nr)))
  protected List<ForbiddenAssignment> forbidden;

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
