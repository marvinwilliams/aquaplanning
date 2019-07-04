package edu.kit.aquaplanning.planning.sat;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.kit.aquaplanning.Configuration;
import edu.kit.aquaplanning.grounding.ArgumentCombinationUtils.Iterator;
import edu.kit.aquaplanning.grounding.PlanningGraphGrounder;
import edu.kit.aquaplanning.grounding.Preprocessor;
import edu.kit.aquaplanning.model.ground.OperatorPlan;
import edu.kit.aquaplanning.model.lifted.Argument;
import edu.kit.aquaplanning.model.lifted.Operator;
import edu.kit.aquaplanning.model.lifted.PlanningProblem;
import edu.kit.aquaplanning.model.lifted.Predicate;
import edu.kit.aquaplanning.model.lifted.Type;
import edu.kit.aquaplanning.model.lifted.condition.AbstractCondition;
import edu.kit.aquaplanning.model.lifted.condition.AbstractCondition.ConditionType;
import edu.kit.aquaplanning.model.lifted.condition.Condition;
import edu.kit.aquaplanning.model.lifted.condition.ConditionSet;
import edu.kit.aquaplanning.planning.LiftedPlanner;
import edu.kit.aquaplanning.planning.sat.LiftedSatUtils.ArgumentAssignment;
import edu.kit.aquaplanning.planning.sat.LiftedSatUtils.ArgumentMapping;
import edu.kit.aquaplanning.planning.sat.LiftedSatUtils.Clause;
import edu.kit.aquaplanning.planning.sat.LiftedSatUtils.ConditionSupport;
import edu.kit.aquaplanning.sat.IpasirSatSolver;
import edu.kit.aquaplanning.sat.SatFormula;
import edu.kit.aquaplanning.sat.SymbolicReachabilityFormula;
import edu.kit.aquaplanning.sat.SymbolicReachabilitySolver;
import edu.kit.aquaplanning.util.Logger;
import edu.kit.aquaplanning.util.Pair;

public class SequentialLiftedSatPlanner extends LiftedPlanner {
  public SequentialLiftedSatPlanner(Configuration config) {
    super(config);
  }

  // parameterIndex is free index
  private int getParameterSatVar(int parameterIndex, Argument argument) {
    int argumentIndex = constantsIndexMap.get(argument);
    return parameterSatVars.get(parameterIndex).get(argumentIndex);
  }

  private Clause implyCondition(ArgumentAssignment assignment) {
    int operatorIndex = operatorIndexMap.get(assignment.getOperator());
    Clause clause = new Clause();

    clause.add(-operatorSatVars.get(operatorIndex));
    for (int i = 0; i < assignment.size(); i++) {
      Argument arg = assignment.getArguments().get(i);
      clause.add(-getParameterSatVar(assignment.getOperatorPos(i), arg));
    }
    return clause;
  }

  private int getConditionSatVar(Condition condition, boolean isNegated, boolean thisStep) {
    if (condition.getPredicate().getName().equals("=")) {
      if (isNegated != condition.getArguments().get(0).equals(condition.getArguments().get(1))) {
        return SAT;
      } else {
        return -SAT;
      }
    }
    int cIdx = conditions.indexOf(condition);
    return (isNegated ? -1 : 1) * (conditionSatVars.get(cIdx) + (thisStep ? 0 : numVars));
  }

  private List<Condition> getConditionList(AbstractCondition condition) {
    Pair<ConditionSet, ConditionSet> split = grounder.splitCondition(condition);
    List<Condition> conditionList = new ArrayList<>();
    if (!split.getRight().getConditions().isEmpty()) {
      Logger.log(Logger.WARN, "Complex conditions are ignored");
    }
    for (AbstractCondition c : split.getLeft().getConditions()) {
      if (c.getConditionType() != ConditionType.atomic) {
        Logger.log(Logger.WARN, "Conditions are expected to be atomic");
      }
      conditionList.add((Condition) c);
    }
    return conditionList;
  }

  private void parameterImpliesCondition(ArgumentAssignment assignment, boolean isNegated, boolean isEffect) {
    Clause clause = implyCondition(assignment);

    Condition condition = assignment.getGroundedCondition();
    clause.add(getConditionSatVar(condition, isNegated, !isEffect));
    // System.out.println(clause);
    if (isEffect) {
      encoding.transitionClauses.addClause(clause.toArray());
    } else {
      encoding.universalClauses.addClause(clause.toArray());
    }
    picClauses++;
  }

  public void atMostOneParameter() {
    for (int oIdx = 0; oIdx < operators.size(); oIdx++) {
      // System.out.println("Operator " +
      Operator o = operators.get(oIdx);
      for (int pIdx = 0; pIdx < o.getArguments().size(); pIdx++) {
        {
          // Operator -> Parameter
          Clause clause = new Clause();
          clause.add(-operatorSatVars.get(oIdx));
          for (Argument arg : constantsOfType.get(o.getArgumentTypes().get(pIdx))) {
            clause.add(getParameterSatVar(pIdx, arg));
          }
          encoding.universalClauses.addClause(clause.toArray());
          amopClauses++;
          // System.out.println("Operator -> parameter");
          // System.out.println(Arrays.toString(clause));
        }
        {
          // AMO Parameter
          Clause clause = new Clause();
          clause.add(parameterSatVars.get(pIdx));
          encoding.universalClauses.addAtMostOneGroup(clause.toArray());
          amopClauses += parameterSatVars.get(pIdx).size() * (parameterSatVars.get(pIdx).size() - 1) / 2;
        }
      }
    }
    // Only one operator
    Clause clause = new Clause();
    clause.add(operatorSatVars);
    encoding.universalClauses.addAtMostOneGroup(clause.toArray());
    amopClauses += operatorSatVars.size() * (operatorSatVars.size() - 1) / 2;
  }

  public void parametersImplyConditions(boolean asEffect) {
    for (int oIdx = 0; oIdx < operators.size(); oIdx++) {
      Operator operator = operators.get(oIdx);
      // System.out.println("Operator " + partiallyGroundedOperator.getName());
      List<Condition> conditionList;
      if (asEffect) {
        conditionList = getConditionList(operator.getEffect());
      } else {
        conditionList = getConditionList(operator.getPrecondition());
      }
      // System.out.println("Operator " + operator);
      for (Condition condition : conditionList) {
        // System.out
        // .println("Condition " + condition + " is " + condition.isNegated());
        // System.out.println(condition);
        ArgumentMapping mapping = new ArgumentMapping(operator, condition);
        List<List<Argument>> args = new ArrayList<>();
        for (int i = 0; i < mapping.size(); i++) {
          args.add(constantsOfType.get(operator.getArgumentTypes().get(mapping.getOperatorPos(i))));
        }
        Iterator argumentIterator = new Iterator(args);
        while (argumentIterator.hasNext()) {
          List<Argument> groundedArgs = argumentIterator.next();
          ArgumentAssignment assignment = new ArgumentAssignment(operator, condition, groundedArgs);
          parameterImpliesCondition(assignment, condition.isNegated(), asEffect);
          if (!condition.getPredicate().getName().equals("=")) {
            conditionSupport.addAssignment(assignment, condition.isNegated(), asEffect);
            // System.out.println("Added " + assignment.getGroundedCondition()
            // + " " + condition.isNegated() + " " + asEffect);
          }
        }
      }
    }
  }

  public void frameAxioms(boolean isNegated) {
    for (Condition condition : conditions) {
      // System.out.println("Condition " + condition + " " + isNegated);
      List<int[]> dnf = new ArrayList<>();
      dnf.add(new int[] { getConditionSatVar(condition, isNegated, true) });
      dnf.add(new int[] { getConditionSatVar(condition, !isNegated, false) });
      List<ArgumentAssignment> assignmentList = conditionSupport.getAssignments(condition, isNegated, true);
      for (ArgumentAssignment assignment : assignmentList) {
        // System.out.println("Support from operator " + assignment.getOperator()
        // + " with arguments " + assignment.getArguments());
        int operatorIndex = operatorIndexMap.get(assignment.getOperator());
        Clause clause = new Clause();
        clause.add(operatorSatVars.get(operatorIndex));
        for (int i = 0; i < assignment.size(); i++) {
          clause.add(getParameterSatVar(assignment.getOperatorPos(i), assignment.getArguments().get(i)));
        }
        dnf.add(clause.toArray());
      }
      encoding.transitionClauses.addDNF(dnf);
      int dnfClauses = 1;
      for (int[] c : dnf) {
        dnfClauses *= c.length;
      }
      frameClauses += dnfClauses;

    }
  }

  void initialState() {
    Clause clause = new Clause();
    for (Condition condition : conditions) {
      if (initialState.contains(condition)) {
        clause.add(getConditionSatVar(condition, false, true));
      } else {
        clause.add(getConditionSatVar(condition, true, true));
      }
    }
    encoding.initialConditions = clause.toArray();
  }

  void goal() {
    Clause clause = new Clause();
    for (Condition condition : goal) {
      clause.add(getConditionSatVar(condition.withoutNegation(), condition.isNegated(), true));
    }
    encoding.goalConditions = clause.toArray();
  }

  public void initializeSatIds() {
    // SAT variable in number 1
    int satVar = 2;
    operatorSatVars = new ArrayList<>();
    parameterSatVars = new ArrayList<>();
    conditionSatVars = new ArrayList<>();
    for (int oIdx = 0; oIdx < operators.size(); oIdx++) {
      operatorSatVars.add(satVar++);
    }
    for (int i = 0; i < maxParams; i++) {
      List<Integer> singleParamSatVars = new ArrayList<>();
      for (int j = 0; j < constants.size(); j++) {
        singleParamSatVars.add(satVar++);
      }
      parameterSatVars.add(singleParamSatVars);
    }
    for (int i = 0; i < conditions.size(); i++) {
      conditionSatVars.add(satVar++);
    }
    // System.out.println("Operator sat vars");
    // for (int i = 0; i < partiallyGroundedOperators.size(); i++) {
    // System.out.println("Operator " +
    // partiallyGroundedOperators.get(i).getName()
    // + ": " + operatorSatVars.get(i));
    // System.out.println(parameterSatVars.get(i));
    // }
    // System.out.println("Condition sat vars");
    // System.out.println(conditionSatVars);
    numVars = satVar - 1;
    encoding = new SymbolicReachabilityFormula();
    encoding.universalClauses = new SatFormula(numVars);
    encoding.transitionClauses = new SatFormula(numVars);
  }

  @Override
  public OperatorPlan plan(PlanningProblem problem) {
    Logger.log(Logger.INFO, "TIME_INIT");
    new Preprocessor(config).preprocess(problem);
    this.problem = problem;
    // System.out.println(problem);
    grounder = new PlanningGraphGrounder(config);
    initialState = new HashSet<>();
    initialState.addAll(problem.getInitialState());
    operators = problem.getOperators();
    operatorIndexMap = new HashMap<>();
    for (Operator o : operators) {
      operatorIndexMap.put(o, operatorIndexMap.size());
    }
    constants = problem.getConstants();
    constantsIndexMap = new HashMap<>();
    for (Argument arg : constants) {
      constantsIndexMap.put(arg, constantsIndexMap.size());
    }
    // System.out.println("Initial operators");
    // System.out.println(problem);
    Logger.log(Logger.INFO, "TIME_GROUND");
    // System.out.println("Initial operators 2");
    // System.out.println(problem);
    // System.out.println("Initial grounded operators");
    // System.out.println(grounder.getFilteredActions());
    // System.out.println("Final state");
    // System.out.println(grounder.getState());
    goal = new ArrayList<>();
    for (AbstractCondition abstractCondition : problem.getGoals()) {
      goal.addAll(getConditionList(abstractCondition));
    }
    // System.out.println("Init: " + initialState);
    // System.out.println("Goal: " + goal);
    Logger.log(Logger.INFO, "TIME_PART");

    conditions = new ArrayList<>();
    constantsOfType = new HashMap<>();
    for (Predicate p : problem.getPredicates().values()) {
      if (p.getName().equals("=")) {
        continue;
      }
      List<List<Argument>> args = new ArrayList<>();
      for (Type t : p.getArgumentTypes()) {
        if (!constantsOfType.containsKey(t)) {
          List<Argument> argList = new ArrayList<>();
          for (Argument arg : constants) {
            if (problem.isArgumentOfType(arg, t)) {
              argList.add(arg);
            }
          }
          constantsOfType.put(t, argList);
        }
        args.add(constantsOfType.get(t));
      }
      Iterator argumentIterator = new Iterator(args);
      while (argumentIterator.hasNext()) {
        List<Argument> groundedArgs = argumentIterator.next();
        Condition condition = new Condition(p);
        for (Argument a : groundedArgs) {
          condition.addArgument(a);
        }
        conditions.add(condition);
      }
    }
    // System.out.println("Conditions: " + conditions);
    // System.out.println("Partially grounded");
    // System.out.println(partiallyGroundedOperators);
    // eligibleArgumentCombinations = new ArrayList<>();
    // Setup the relevant operators for lookup
    maxParams = 0;
    for (Operator o : operators) {
      for (Type t : o.getArgumentTypes()) {
        if (!constantsOfType.containsKey(t)) {
          List<Argument> argList = new ArrayList<>();
          for (Argument arg : constants) {
            if (problem.isArgumentOfType(arg, t)) {
              argList.add(arg);
            }
          }
          constantsOfType.put(t, argList);
        }
      }
      if (o.getArguments().size() > maxParams) {
        maxParams = o.getArguments().size();
      }
    }
    // System.out.println(possibleArguments);
    // Iterate over all operators to collect parameter information and
    // conditions
    // System.out.println("Partially grounded operators");
    // System.out.println(partiallyGroundedOperators);
    // System.out.println("All conditions");
    // System.out.println(conditions);

    initializeSatIds();
    amopClauses = 0;
    picClauses = 0;
    ifrClauses = 0;
    frameClauses = 0;
    Logger.log(Logger.INFO, "NUM_VARS " + numVars);
    encoding = new SymbolicReachabilityFormula();
    encoding.universalClauses = new SatFormula(numVars);
    encoding.transitionClauses = new SatFormula(numVars);
    encoding.universalClauses.addClause(new int[] { SAT });
    conditionSupport = new ConditionSupport();
    atMostOneParameter();
    parametersImplyConditions(false);
    parametersImplyConditions(true);
    frameAxioms(false);
    frameAxioms(true);
    initialState();
    goal();
    Logger.log(Logger.INFO, "NUM_AMOP " + amopClauses);
    Logger.log(Logger.INFO, "NUM_PIC " + picClauses);
    Logger.log(Logger.INFO, "NUM_IFR " + ifrClauses);
    Logger.log(Logger.INFO, "NUM_FRAME " + frameClauses);
    Logger.log(Logger.INFO, "TIME_GEN");
    SymbolicReachabilitySolver solver = new SymbolicReachabilitySolver(new IpasirSatSolver());
    List<int[]> model = solver.solve(encoding);
    // System.out.println(model);
    Logger.log(Logger.INFO, "TIME_FINISH");
    OperatorPlan plan = extractPlan(model);
    // System.out.println("Done planning");
    return plan;
  }

  protected OperatorPlan extractPlan(List<int[]> model) {
    OperatorPlan plan = new OperatorPlan();
    for (int i = 0; i < model.size(); i++) {
      for (int oIdx = 0; oIdx < operators.size(); oIdx++) {
        Operator operator = operators.get(oIdx);
        if (model.get(i)[operatorSatVars.get(oIdx)] > 0) {
          List<Argument> args = new ArrayList<>();
          for (int pos = 0; pos < operator.getArguments().size(); pos++) {
            args.add(null);
          }
          for (int j = 0; j < operator.getArguments().size(); j++) {
            boolean found = false;
            for (Argument arg : constantsOfType.get(operator.getArgumentTypes().get(j))) {
              if (model.get(i)[getParameterSatVar(j, arg)] >= 0) {
                args.set(j, arg);
                found = true;
                break;
              }
            }
            if (!found) {
              Logger.log(Logger.ERROR, "Parameter not set in solution");
              System.exit(1);
            }
          }
          Operator groundedOperator = operator.getOperatorWithGroundArguments(args);
          // System.out.println("Plan " + groundedOperator);
          plan.appendAtBack(groundedOperator);
          break;
        }
      }
    }
    return plan;
  }

  private static int SAT = 1;
  private Set<Condition> initialState;
  private List<Condition> goal;
  private PlanningGraphGrounder grounder;
  private ConditionSupport conditionSupport;
  private int amopClauses;
  private int picClauses;
  private int ifrClauses;
  private int frameClauses;

  private SymbolicReachabilityFormula encoding;
  private List<Integer> operatorSatVars;
  private List<List<Integer>> parameterSatVars;
  private List<Integer> conditionSatVars;
  private int numVars;
  private int maxParams;

  private List<Operator> operators;
  private List<Condition> conditions;
  private List<Argument> constants;
  private Map<Operator, Integer> operatorIndexMap;
  private Map<Argument, Integer> constantsIndexMap;
  private Map<Type, List<Argument>> constantsOfType;
}
