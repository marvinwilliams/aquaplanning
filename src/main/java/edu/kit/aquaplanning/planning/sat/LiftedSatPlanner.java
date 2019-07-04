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
import edu.kit.aquaplanning.model.ground.OperatorPlan;
import edu.kit.aquaplanning.model.lifted.Argument;
import edu.kit.aquaplanning.model.lifted.Operator;
import edu.kit.aquaplanning.model.lifted.PlanningProblem;
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

public class LiftedSatPlanner extends LiftedPlanner {
  public LiftedSatPlanner(Configuration config) {
    super(config);
  }

  private class OperatorParameterList {
    public OperatorParameterList(Operator operator) {
      numOperators = 0;
      freeParameters = new ArrayList<>();
      argumentList = new ArrayList<>();
      for (int i = 0; i < operator.getArguments().size(); i++) {
        if (!operator.getArguments().get(i).isConstant()) {
          freeParameters.add(i);
          argumentList.add(new ArrayList<>());
        }
      }
    }

    public int getNumOperators() {
      return numOperators;
    }

    public void addOperator(Operator operator) {
      for (int i = 0; i < freeParameters.size(); i++) {
        Argument arg = operator.getArguments().get(freeParameters.get(i));
        if (!argumentList.get(i).contains(arg)) {
          argumentList.get(i).add(arg);
        }
      }
      numOperators += 1;
    }

    public int numFreeParameters() {
      return freeParameters.size();
    }

    public int getFreeParameter(int i) {
      return freeParameters.get(i);
    }

    public List<Argument> getPossibleArguments(int i) {
      return argumentList.get(i);
    }

    public List<List<Argument>> getPossibleArguments(ArgumentMapping mapping) {
      List<List<Argument>> args = new ArrayList<>();
      for (int i = 0; i < mapping.size(); i++) {
        // The index of the i'th free parameter
        int operatorPos = mapping.getOperatorPos(i);
        args.add(argumentList.get(operatorPos));
      }
      return args;
    }

    private List<List<Argument>> argumentList;
    private List<Integer> freeParameters;
    private int numOperators;
  }

  public boolean[] computeGroundArguments(Operator operator, OperatorParameterList possibleArgs) {
    boolean bestGrounding[] = new boolean[possibleArgs.numFreeParameters()];
    if (possibleArgs.getNumOperators() == 0) {
      return bestGrounding;
    }
    // System.out.println("Compute grounding for " + operator.getName());
    List<List<Condition>> dependentConditions = new ArrayList<>();
    while (dependentConditions.size() < possibleArgs.numFreeParameters()) {
      dependentConditions.add(new ArrayList<>());
    }
    Map<Condition, Integer> freeCounter = new HashMap<>();
    for (Condition condition : getConditionList(operator.getEffect())) {
      int counter = 0;
      for (Argument arg : condition.getArguments()) {
        if (arg.isConstant()) {
          continue;
        }
        for (int i = 0; i < possibleArgs.numFreeParameters(); i++) {
          if (arg.equals(operator.getArguments().get(possibleArgs.getFreeParameter(i)))) {
            dependentConditions.get(i).add(condition);
            break;
          }
        }
        counter++;
      }
      freeCounter.put(condition, counter);
    }
    boolean currentGrounding[] = new boolean[possibleArgs.numFreeParameters()];
    int best = Integer.MAX_VALUE;
    for (int i = 0; i <= possibleArgs.numFreeParameters(); i++) {
      best = computeGrounding(possibleArgs, dependentConditions, freeCounter, i, best, bestGrounding, 0, 1,
          currentGrounding);
    }
    return bestGrounding;
  }

  private int computeGrounding(OperatorParameterList possibleArgs, List<List<Condition>> dependentConditions,
      Map<Condition, Integer> freeCounter, int maxGrounded, int currentBest, boolean[] bestGrounding, int currentPos,
      int current, boolean[] currentGrounding) {
    if (current >= currentBest) {
      return currentBest;
    }
    if (maxGrounded == 0) {
      boolean valid = true;
      for (int free : freeCounter.values()) {
        if (free > 1) {
          valid = false;
          break;
        }
      }
      if (valid) {
        System.arraycopy(currentGrounding, 0, bestGrounding, 0, currentGrounding.length);
        currentBest = current;
      }
      return currentBest;
    } else {
      for (int pos = currentPos; pos <= possibleArgs.numFreeParameters() - maxGrounded; pos++) {
        if (dependentConditions.get(pos).size() == 0) {
          // Grounding this parameter has no effect
          continue;
        }
        currentGrounding[pos] = true;
        for (Condition condition : dependentConditions.get(pos)) {
          freeCounter.put(condition, freeCounter.get(condition) - 1);
        }
        current *= possibleArgs.getPossibleArguments(pos).size();
        currentBest = computeGrounding(possibleArgs, dependentConditions, freeCounter, maxGrounded - 1, currentBest,
            bestGrounding, pos + 1, current, currentGrounding);
        current /= possibleArgs.getPossibleArguments(pos).size();
        for (Condition condition : dependentConditions.get(pos)) {
          freeCounter.put(condition, freeCounter.get(condition) + 1);
        }
        currentGrounding[pos] = false;
      }
    }
    return currentBest;
  }

  // parameterIndex is free index
  private int getArgumentIndex(int operatorIndex, int parameterIndex, Argument argument) {
    return possibleArguments.get(operatorIndex).getPossibleArguments(parameterIndex).indexOf(argument);
  }

  // parameterIndex is free index
  private int getParameterSatVar(int operatorIndex, int parameterIndex, Argument argument) {
    int argumentIndex = getArgumentIndex(operatorIndex, parameterIndex, argument);
    return getParameterSatVar(operatorIndex, parameterIndex, argumentIndex);
  }

  private int getParameterSatVar(int operatorIndex, int parameterIndex, int argumentIndex) {
    List<Integer> satVars = parameterSatVars.get(operatorIndex).get(parameterIndex);
    return satVars.get(argumentIndex);
  }

  private Clause implyCondition(ArgumentAssignment assignment) {
    int operatorIndex = operatorIndexMap.get(assignment.getOperator());
    Clause clause = new Clause();

    clause.add(-operatorSatVars.get(operatorIndex));
    for (int i = 0; i < assignment.size(); i++) {
      Argument arg = assignment.getArguments().get(i);
      clause.add(-getParameterSatVar(operatorIndex, assignment.getOperatorPos(i), arg));
    }
    return clause;
  }

  private int getConditionSatVar(Condition condition, boolean isNegated, boolean thisStep) {
    int cIdx = conditions.indexOf(condition);
    if (cIdx == -1) {
      // If the condition is not known, it is either rigid true or false
      if (isNegated != (initialState.contains(condition) || (condition.getPredicate().getName().equals("=")
          && (condition.getArguments().get(0).equals(condition.getArguments().get(1)))))) {
        return SAT;
      } else {
        return -SAT;
      }
    }
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

  public void parameterImpliesCondition(ArgumentAssignment assignment, boolean isNegated, boolean isEffect) {
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
      // partiallyGroundedOperators.get(oIdx).getName());
      for (int pIdx = 0; pIdx < possibleArguments.get(oIdx).numFreeParameters(); pIdx++) {
        int numArgs = possibleArguments.get(oIdx).getPossibleArguments(pIdx).size();
        {
          // Operator -> Parameter
          Clause clause = new Clause();
          clause.add(-operatorSatVars.get(oIdx));
          for (int aIdx = 0; aIdx < numArgs; aIdx++) {
            clause.add(getParameterSatVar(oIdx, pIdx, aIdx));
          }
          encoding.universalClauses.addClause(clause.toArray());
          amopClauses++;
          // System.out.println("Operator -> parameter");
          // System.out.println(Arrays.toString(clause));
        }
        {
          // Parameter -> Operator
          for (int aIdx = 0; aIdx < numArgs; aIdx++) {
            Clause clause = new Clause();
            clause.add(-getParameterSatVar(oIdx, pIdx, aIdx));
            clause.add(operatorSatVars.get(oIdx));
            encoding.universalClauses.addClause(clause.toArray());
            amopClauses++;
            // System.out.println("Parameter -> Operator");
            // System.out.println(Arrays.toString(clause));
          }
        }
        // AMO Parameter
        Clause clause = new Clause();
        clause.add(parameterSatVars.get(oIdx).get(pIdx));
        encoding.universalClauses.addAtMostOneGroup(clause.toArray());
        amopClauses += parameterSatVars.get(oIdx).get(pIdx).size() * (parameterSatVars.get(oIdx).get(pIdx).size() - 1)
            / 2;
      }
    }
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
      for (Condition condition : conditionList) {
        // System.out.println(condition);
        ArgumentMapping mapping = new ArgumentMapping(operator, condition);
        List<List<Argument>> args = possibleArguments.get(oIdx).getPossibleArguments(mapping);
        Iterator argumentIterator = new Iterator(args);
        // will be called once with empty args
        while (argumentIterator.hasNext()) {
          List<Argument> groundedArgs = argumentIterator.next();
          ArgumentAssignment assignment = new ArgumentAssignment(operator, condition, groundedArgs);
          parameterImpliesCondition(assignment, condition.isNegated(), asEffect);
          picClauses++;
          if (conditions.contains(assignment.getGroundedCondition())) {
            conditionSupport.addAssignment(assignment, condition.isNegated(), asEffect);
          }
        }
      }
    }
  }

  public void interference(boolean isNegated) {
    for (Condition condition : conditions) {
      for (ArgumentAssignment preconditionAssignment : conditionSupport.getAssignments(condition, isNegated, false)) {
        for (ArgumentAssignment effectAssignment : conditionSupport.getAssignments(condition, !isNegated, true)) {
          if (preconditionAssignment.getOperator().equals(effectAssignment.getOperator())) {
            continue;
          }
          forbidParameters(preconditionAssignment, effectAssignment);
        }
      }
    }
  }

  public void forbidParameters(ArgumentAssignment first, ArgumentAssignment second) {
    Clause clause = new Clause();
    clause.add(implyCondition(first));
    clause.add(implyCondition(second));
    encoding.universalClauses.addClause(clause.toArray());
    ifrClauses++;
  }

  public void frameAxioms(boolean isNegated) {
    for (Condition condition : conditions) {
      List<int[]> dnf = new ArrayList<>();
      dnf.add(new int[] { getConditionSatVar(condition, isNegated, true) });
      dnf.add(new int[] { getConditionSatVar(condition, !isNegated, false) });
      List<ArgumentAssignment> assignmentList = conditionSupport.getAssignments(condition, isNegated, true);
      // System.out.println("Condition " + condition + " " + isNegated);
      for (ArgumentAssignment assignment : assignmentList) {
        // System.out.println(
        // assignment.getOperator() + " with " + assignment.getArguments());
        int operatorIndex = operatorIndexMap.get(assignment.getOperator());
        Clause clause = new Clause();
        if (assignment.size() == 0) {
          clause.add(operatorSatVars.get(operatorIndex));
        } else {
          for (int i = 0; i < assignment.size(); i++) {
            clause
                .add(getParameterSatVar(operatorIndex, assignment.getOperatorPos(i), assignment.getArguments().get(i)));
          }
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
      List<List<Integer>> operatorParamSatVars = new ArrayList<>();
      int numParams = possibleArguments.get(oIdx).numFreeParameters();
      for (int pIdx = 0; pIdx < numParams; pIdx++) {
        List<Integer> argSatVars = new ArrayList<>();
        int numArgs = possibleArguments.get(oIdx).getPossibleArguments(pIdx).size();
        for (int k = 0; k < numArgs; k++) {
          argSatVars.add(satVar++);
        }
        operatorParamSatVars.add(argSatVars);
      }
      parameterSatVars.add(operatorParamSatVars);
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

  public void setOperators(List<Operator> liftedOperators, List<Operator> groundedOperators) {
    Map<String, Integer> operatorIndex = new HashMap<String, Integer>();
    List<OperatorParameterList> operatorArgs = new ArrayList<>();
    // Set up the lookup to the lifted operators
    for (Operator o : liftedOperators) {
      String name = o.getName();
      operatorIndex.put(name, operatorIndex.size());
      operatorArgs.add(new OperatorParameterList(o));
    }
    // List the sets of arguments of the lifted operators to determine the
    // arguments
    // to ground
    for (Operator o : groundedOperators) {
      int idx = operatorIndex.get(o.getName());
      operatorArgs.get(idx).addOperator(o);
    }
    // Get the list of grounded arguments
    List<boolean[]> operatorArgumentsToGround = new ArrayList<>();
    for (Operator o : liftedOperators) {
      int idx = operatorIndex.get(o.getName());
      operatorArgumentsToGround.add(computeGroundArguments(o, operatorArgs.get(idx)));
    }
    operators = new ArrayList<Operator>();
    operatorIndexMap = new HashMap<>();
    operatorLookup = new ArrayList<>();
    // Get the partially grounded operator for each grounded operator
    for (Operator o : groundedOperators) {
      int idx = operatorIndex.get(o.getName());
      Operator liftedOperator = liftedOperators.get(idx);
      List<Argument> args = new ArrayList<>();
      int counter = 0;
      for (int i = 0; i < liftedOperator.getArguments().size(); i++) {
        if (liftedOperator.getArguments().get(i).isConstant()) {
          args.add(null);
        } else {
          if (operatorArgumentsToGround.get(idx)[counter]) {
            args.add(o.getArguments().get(i));
          } else {
            args.add(null);
          }
          counter++;
        }
      }
      Operator partiallyGroundedOperator = liftedOperator.getOperatorWithGroundArguments(args);
      int lookupIdx = operatorIndexMap.getOrDefault(partiallyGroundedOperator, -1);
      if (lookupIdx == -1) {
        lookupIdx = operators.size();
        operators.add(partiallyGroundedOperator);
        operatorIndexMap.put(partiallyGroundedOperator, lookupIdx);
      }
      operatorLookup.add(lookupIdx);
    }
  }

  @Override
  public OperatorPlan plan(PlanningProblem problem) {
    Logger.log(Logger.INFO, "TIME_INIT");
    this.problem = problem;
    initialState = new HashSet<>();
    initialState.addAll(problem.getInitialState());
    // System.out.println("Initial operators");
    // System.out.println(problem);
    grounder = new PlanningGraphGrounder(config);
    grounder.ground(problem);
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
    setOperators(problem.getOperators(), grounder.getFilteredActions());
    Logger.log(Logger.INFO, "TIME_PART");
    // System.out.println("Partially grounded");
    // System.out.println(partiallyGroundedOperators);
    // eligibleArgumentCombinations = new ArrayList<>();
    possibleArguments = new ArrayList<>();
    Set<Condition> conditionSet = new HashSet<>();
    // Setup the relevant operators for lookup
    for (Operator o : operators) {
      possibleArguments.add(new OperatorParameterList(o));
    }
    // Iterate over all operators to collect parameter information and
    // conditions
    for (int op = 0; op < grounder.getFilteredActions().size(); op++) {
      Operator groundedOperator = grounder.getFilteredActions().get(op);
      int idx = operatorLookup.get(op);
      possibleArguments.get(idx).addOperator(groundedOperator);
      {
        List<Condition> conditions = getConditionList(groundedOperator.getPrecondition());
        for (Condition condition : conditions) {
          conditionSet.add(condition.withoutNegation());
        }
      }
      {
        List<Condition> conditions = getConditionList(groundedOperator.getEffect());
        for (Condition condition : conditions) {
          conditionSet.add(condition.withoutNegation());
        }
      }
    }
    // System.out.println("Partially grounded operators");
    // System.out.println(partiallyGroundedOperators);
    conditions = new ArrayList<>(conditionSet);
    // System.out.println("All conditions");
    // System.out.println(conditions);
    System.out.println("Init: " + initialState);
    System.out.println("Goal: " + initialState);
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
    interference(false);
    interference(true);
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
          for (int j = 0; j < possibleArguments.get(oIdx).numFreeParameters(); j++) {
            boolean found = false;
            for (Argument arg : possibleArguments.get(oIdx).getPossibleArguments(j)) {
              if (model.get(i)[getParameterSatVar(oIdx, j, arg)] >= 0) {
                args.set(possibleArguments.get(oIdx).getFreeParameter(j), arg);
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
          boolean foundOperator = false;
          for (Operator o : grounder.getFilteredActions()) {
            if (groundedOperator.equals(o)) {
              foundOperator = true;
              plan.appendAtBack(groundedOperator);
              break;
            }
          }
          if (!foundOperator) {
            Logger.log(Logger.ERROR, "Extracted operator not found");
            System.exit(1);
          }
        }
      }
    }
    return plan;
  }

  private static int SAT = 1;
  private Set<Condition> initialState;
  private List<Condition> goal;
  private PlanningGraphGrounder grounder;
  private List<Integer> operatorLookup;
  private ConditionSupport conditionSupport;
  private int amopClauses;
  private int picClauses;
  private int ifrClauses;
  private int frameClauses;

  private SymbolicReachabilityFormula encoding;
  // private List<List<List<Argument>>> eligibleArgumentCombinations;
  private List<OperatorParameterList> possibleArguments;
  private List<Integer> operatorSatVars;
  private List<List<List<Integer>>> parameterSatVars;
  private List<Integer> conditionSatVars;
  private int numVars;

  private List<Operator> operators;
  private Map<Operator, Integer> operatorIndexMap;
  private List<Condition> conditions;
}
