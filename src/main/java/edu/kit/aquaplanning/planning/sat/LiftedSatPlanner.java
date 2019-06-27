package edu.kit.aquaplanning.planning.sat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.kit.aquaplanning.Configuration;
import edu.kit.aquaplanning.planning.sat.LiftedSatUtils;
import edu.kit.aquaplanning.grounding.ArgumentCombinationUtils;
import edu.kit.aquaplanning.grounding.PlanningGraphGrounder;
import edu.kit.aquaplanning.model.ground.GroundPlanningProblem;
import edu.kit.aquaplanning.model.ground.OperatorPlan;
import edu.kit.aquaplanning.model.lifted.Argument;
import edu.kit.aquaplanning.model.lifted.Operator;
import edu.kit.aquaplanning.model.lifted.PlanningProblem;
import edu.kit.aquaplanning.model.lifted.condition.AbstractCondition;
import edu.kit.aquaplanning.model.lifted.condition.AbstractCondition.ConditionType;
import edu.kit.aquaplanning.model.lifted.condition.Condition;
import edu.kit.aquaplanning.model.lifted.condition.ConditionSet;
import edu.kit.aquaplanning.planning.LiftedPlanner;
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

  class OperatorParameterList {
    public OperatorParameterList(Operator o) {
      numOperators = 0;
      freeParameters = new ArrayList<>();
      for (int i = 0; i < o.getArguments().size(); i++) {
        if (!o.getArguments().get(i).isConstant()) {
          freeParameters.add(i);
        }
      }
      argumentList = new ArrayList<>();
      while (argumentList.size() < freeParameters.size()) {
        argumentList.add(new ArrayList<>());
      }
    }

    public int getNumOperators() {
      return numOperators;
    }

    public void addOperator(Operator o) {
      for (int i = 0; i < freeParameters.size(); i++) {
        Argument arg = o.getArguments().get(freeParameters.get(i));
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

    public List<List<Argument>> getPossibleArguments(LiftedSatUtils.ArgumentMapping mapping) {
      List<List<Argument>> args = new ArrayList<>();
      for (int i = 0; i < mapping.size(); i++) {
        int operatorPos = mapping.getOperatorPos(i);
        args.add(argumentList.get(operatorPos));
      }
      return args;
    }

    List<List<Argument>> argumentList;
    List<Integer> freeParameters;
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
        if (!arg.isConstant()) {
          counter++;
          for (int i = 0; i < possibleArgs.numFreeParameters(); i++) {
            if (arg.equals(operator.getArguments().get(possibleArgs.getFreeParameter(i)))) {
              dependentConditions.get(i).add(condition);
              break;
            }
          }
        }
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
    return parameterSatVars.get(operatorIndex).get(parameterIndex).get(argumentIndex);
  }

  private List<Integer> implyCondition(LiftedSatUtils.ArgumentAssignment assignment) {
    int operatorIndex = operatorIndexMap.get(assignment.getMapping().getOperator());
    List<Integer> clause = new ArrayList<>();
    clause.add(-operatorSatVars.get(operatorIndex));
    for (int i = 0; i < assignment.size(); i++) {
      Argument arg = assignment.getArguments().get(i);
      clause.add(-getParameterSatVar(operatorIndex, assignment.getMapping().getOperatorPos(i), arg));
    }
    return clause;
  }

  private int getConditionSatVar(Condition condition, boolean thisStep) {
    int cIdx = conditions.indexOf(condition.withoutNegation());
    if (cIdx == -1) {
      // If the condition is not known, it is either rigid true or false
      if ((condition.isNegated() != initialState.contains(condition)) || (condition.getPredicate().getName().equals("=")
          && condition.getArguments().get(0).equals(condition.getArguments().get(1)))) {
        return SAT;
      } else {
        return -SAT;
      }
    }
    return (condition.isNegated() ? -1 : 1) * (conditionSatVars.get(cIdx) + (thisStep ? 0 : numVars));
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

  public void addParameterImpliesCondition(LiftedSatUtils.ArgumentAssignment assignment, Condition condition,
      boolean isEffect) {
    List<Integer> clause = implyCondition(assignment);
    clause.add(getConditionSatVar(condition, !isEffect));
    // System.out.println(clause);
    if (isEffect) {
      encoding.transitionClauses.addClause(clause.stream().mapToInt(x -> x).toArray());
    } else {
      encoding.universalClauses.addClause(clause.stream().mapToInt(x -> x).toArray());
    }
  }

  public void atMostOneParameter() {
    for (int oIdx = 0; oIdx < partiallyGroundedOperators.size(); oIdx++) {
      // System.out.println("Operator " +
      // partiallyGroundedOperators.get(oIdx).getName());
      for (int pIdx = 0; pIdx < possibleArguments.get(oIdx).numFreeParameters(); pIdx++) {
        {
          // Operator -> Parameter
          int clause[] = new int[possibleArguments.get(oIdx).getPossibleArguments(pIdx).size() + 1];
          int counter = 0;
          clause[counter++] = -operatorSatVars.get(oIdx);
          for (int aIdx = 0; aIdx < possibleArguments.get(oIdx).getPossibleArguments(pIdx).size(); aIdx++) {
            clause[counter++] = getParameterSatVar(oIdx, pIdx, aIdx);
          }
          encoding.universalClauses.addClause(clause);
          amopClauses++;
          // System.out.println("Operator -> parameter");
          // System.out.println(Arrays.toString(clause));
        }
        {
          // Parameter -> Operator
          for (int aIdx = 0; aIdx < possibleArguments.get(oIdx).getPossibleArguments(pIdx).size(); aIdx++) {
            int clause[] = new int[2];
            clause[0] = -getParameterSatVar(oIdx, pIdx, aIdx);
            clause[1] = operatorSatVars.get(oIdx);
            encoding.universalClauses.addClause(clause);
            amopClauses++;
            // System.out.println("Parameter -> Operator");
            // System.out.println(Arrays.toString(clause));
          }
        }
        // AMO Parameter
        encoding.universalClauses
            .addAtMostOneGroup(parameterSatVars.get(oIdx).get(pIdx).stream().mapToInt(x -> x).toArray());
        amopClauses += parameterSatVars.get(oIdx).get(pIdx).size() * (parameterSatVars.get(oIdx).get(pIdx).size() - 1)
            / 2;
      }
    }
  }

  public void parametersImplyConditions() {
    conditionSupport = new LiftedSatUtils.ConditionSupport();
    for (int oIdx = 0; oIdx < partiallyGroundedOperators.size(); oIdx++) {
      Operator partiallyGroundedOperator = partiallyGroundedOperators.get(oIdx);
      // System.out.println("Operator " + partiallyGroundedOperator.getName());
      {
        List<Condition> preconditions = getConditionList(partiallyGroundedOperator.getPrecondition());
        for (Condition condition : preconditions) {
          // System.out.println(condition);
          LiftedSatUtils.ArgumentMapping mapping = new LiftedSatUtils.ArgumentMapping(partiallyGroundedOperator,
              condition);
          List<List<Argument>> args = possibleArguments.get(oIdx).getPossibleArguments(mapping);
          ArgumentCombinationUtils.Iterator argumentIterator = new ArgumentCombinationUtils.Iterator(args);
          argumentIterator.forEachRemaining(groundedArgs -> {
            Condition groundedCondition = condition.getConditionBoundToArguments(mapping.getRefArgs(), groundedArgs);
            LiftedSatUtils.ArgumentAssignment assignment = new LiftedSatUtils.ArgumentAssignment(mapping,
                groundedCondition.getArguments());
            addParameterImpliesCondition(assignment, groundedCondition, false);
            picClauses++;
            if (conditions.contains(groundedCondition.withoutNegation())) {
              conditionSupport.addAssignment(assignment, groundedCondition.isNegated(), false);
            }
          });
        }
      }
      {
        List<Condition> effects = getConditionList(partiallyGroundedOperator.getEffect());
        for (Condition condition : effects) {
          // System.out.println(condition);
          LiftedSatUtils.ArgumentMapping mapping = new LiftedSatUtils.ArgumentMapping(partiallyGroundedOperator,
              condition);
          List<List<Argument>> args = possibleArguments.get(oIdx).getPossibleArguments(mapping);
          ArgumentCombinationUtils.Iterator argumentIterator = new ArgumentCombinationUtils.Iterator(args);
          argumentIterator.forEachRemaining(groundedArgs -> {
            Condition groundedCondition = condition.getConditionBoundToArguments(mapping.getRefArgs(), groundedArgs);
            LiftedSatUtils.ArgumentAssignment assignment = new LiftedSatUtils.ArgumentAssignment(mapping,
                groundedCondition.getArguments());
            addParameterImpliesCondition(assignment, groundedCondition, true);
            picClauses++;
            if (conditions.contains(groundedCondition.withoutNegation())) {
              conditionSupport.addAssignment(assignment, groundedCondition.isNegated(), true);
            }
          });
        }
      }
    }
  }

  public void interfereCondition(Condition condition, boolean isNegated) {
    for (LiftedSatUtils.ArgumentAssignment preconditionAssignment : conditionSupport.getAssignments(condition, false,
        isNegated)) {
      for (LiftedSatUtils.ArgumentAssignment effectAssignment : conditionSupport.getAssignments(condition, true,
          !isNegated)) {
        if (preconditionAssignment.getMapping().getOperator().equals(effectAssignment.getMapping().getOperator())) {
          continue;
        }
        forbidParameters(preconditionAssignment, effectAssignment);
        ifrClauses++;
      }
    }
  }

  public void interference() {
    for (Condition condition : conditions) {
      interfereCondition(condition, false);
      interfereCondition(condition, true);
    }
  }

  public void forbidParameters(LiftedSatUtils.ArgumentAssignment first, LiftedSatUtils.ArgumentAssignment second) {
    List<Integer> clause = new ArrayList<>();
    clause.addAll(implyCondition(first));
    clause.addAll(implyCondition(second));
    encoding.universalClauses.addClause(clause.stream().mapToInt(x -> x).toArray());
  }

  public void frameAxiomCondition(Condition condition, boolean isNegated) {
    List<int[]> dnf = new ArrayList<>();
    dnf.add(new int[] { (isNegated ? -1 : 1) * getConditionSatVar(condition, true) });
    dnf.add(new int[] { (isNegated ? 1 : -1) * getConditionSatVar(condition, false) });
    List<LiftedSatUtils.ArgumentAssignment> assignmentList = conditionSupport.getAssignments(condition, isNegated,
        true);
    if (assignmentList.size() == 0) {
      Logger.log(Logger.WARN, "no assignment supports positive condition " + condition);
    }
    for (LiftedSatUtils.ArgumentAssignment assignment : assignmentList) {
      int operatorIndex = operatorIndexMap.get(assignment.getMapping().getOperator());
      if (assignment.size() == 0) {
        dnf.add(new int[] { operatorSatVars.get(operatorIndex) });
      } else {
        int[] clause = new int[assignment.size()];
        for (int i = 0; i < assignment.size(); i++) {
          clause[i] = getParameterSatVar(operatorIndex, assignment.getMapping().getOperatorPos(i),
              assignment.getArguments().get(i));
        }
        dnf.add(clause);
      }
    }
    encoding.transitionClauses.addDNF(dnf);
    int dnfClauses = 1;
    for (int[] c : dnf) {
      dnfClauses *= c.length;
    }
    frameClauses += dnfClauses;
  }

  public void frameAxioms() {
    for (Condition condition : conditions) {
      frameAxiomCondition(condition, false);
      frameAxiomCondition(condition, true);
    }
  }

  void initialState() {
    List<Integer> clause = new ArrayList<>();
    for (Condition condition : conditions) {
      if (initialState.contains(condition)) {
        clause.add(getConditionSatVar(condition, true));
      } else {
        clause.add(-getConditionSatVar(condition, true));
      }
    }
    encoding.initialConditions = clause.stream().mapToInt(x -> x).toArray();
  }

  void goal() {
    List<Integer> clause = new ArrayList<>();
    for (Condition condition : goal) {
      clause.add(getConditionSatVar(condition, true));
    }
    encoding.goalConditions = clause.stream().mapToInt(x -> x).toArray();
  }

  public void initializeSatIds() {
    // SAT variable in number 1
    int satVar = 2;
    operatorSatVars = new ArrayList<>();
    parameterSatVars = new ArrayList<>();
    conditionSatVars = new ArrayList<>();
    for (int oIdx = 0; oIdx < partiallyGroundedOperators.size(); oIdx++) {
      operatorSatVars.add(satVar++);
      parameterSatVars.add(new ArrayList<>());
      for (int pIdx = 0; pIdx < possibleArguments.get(oIdx).numFreeParameters(); pIdx++) {
        parameterSatVars.get(oIdx).add(new ArrayList<>());
        for (int k = 0; k < possibleArguments.get(oIdx).getPossibleArguments(pIdx).size(); k++) {
          parameterSatVars.get(oIdx).get(pIdx).add(satVar++);
        }
      }
    }
    for (int i = 0; i < conditions.size(); i++) {
      conditionSatVars.add(satVar++);
    }
    // System.out.println("Operator sat vars");
    // for (int i = 0; i < partiallyGroundedOperators.size(); i++) {
    // System.out.println("Operator " + partiallyGroundedOperators.get(i).getName()
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

  public void setPartiallyGroundedOperators(List<Operator> liftedOperators, List<Operator> groundedOperators) {
    Map<String, Integer> operatorIndex = new HashMap<String, Integer>();
    List<OperatorParameterList> operatorArgs = new ArrayList<>();
    // Set up the lookup to the lifted operators
    for (Operator o : liftedOperators) {
      String name = o.getName();
      operatorIndex.put(name, operatorIndex.size());
      operatorArgs.add(new OperatorParameterList(o));
    }
    // List the sets of arguments of the lifted operators to determine the arguments
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
    partiallyGroundedOperators = new ArrayList<Operator>();
    operatorIndexMap = new HashMap<>();
    partiallyGroundedOperatorLookup = new ArrayList<>();
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
        lookupIdx = partiallyGroundedOperators.size();
        partiallyGroundedOperators.add(partiallyGroundedOperator);
        operatorIndexMap.put(partiallyGroundedOperator, operatorIndexMap.size());
      }
      partiallyGroundedOperatorLookup.add(lookupIdx);
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
    GroundPlanningProblem groundedProblem = grounder.ground(problem);
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
    setPartiallyGroundedOperators(problem.getOperators(), grounder.getFilteredActions());
    Logger.log(Logger.INFO, "TIME_PART");
    // System.out.println("Partially grounded");
    // System.out.println(partiallyGroundedOperators);
    // eligibleArgumentCombinations = new ArrayList<>();
    possibleArguments = new ArrayList<>();
    Set<Condition> conditionSet = new HashSet<>();
    // Setup the relevant operators for lookup
    for (Operator o : partiallyGroundedOperators) {
      possibleArguments.add(new OperatorParameterList(o));
    }
    // Iterate over all operators to collect parameter information and conditions
    for (int op = 0; op < grounder.getFilteredActions().size(); op++) {
      Operator groundedOperator = grounder.getFilteredActions().get(op);
      int idx = partiallyGroundedOperatorLookup.get(op);
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
    atMostOneParameter();
    parametersImplyConditions();
    interference();
    frameAxioms();
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
      for (int oIdx = 0; oIdx < partiallyGroundedOperators.size(); oIdx++) {
        Operator operator = partiallyGroundedOperators.get(oIdx);
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
  private List<Integer> partiallyGroundedOperatorLookup;
  private LiftedSatUtils.ConditionSupport conditionSupport;
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

  private List<Operator> partiallyGroundedOperators;
  private Map<Operator, Integer> operatorIndexMap;
  private List<Condition> conditions;
}
