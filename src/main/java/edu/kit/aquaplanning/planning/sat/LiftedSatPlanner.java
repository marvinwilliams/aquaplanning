package edu.kit.aquaplanning.planning.sat;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.kit.aquaplanning.Configuration;
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

  class ArgumentMapping {
    public ArgumentMapping(Operator operator, Condition condition) {
      operatorIndex = partiallyGroundedOperators.indexOf(operator);
      init(operator, condition.withoutNegation());
    }

    public ArgumentMapping(int operatorIndex, Condition condition) {
      this.operatorIndex = operatorIndex;
      Operator o = partiallyGroundedOperators.get(operatorIndex);
      init(o, condition.withoutNegation());
    }

    protected void init(Operator operator, Condition condition) {
      size = 0;
      conditionPos = new ArrayList<>();
      operatorPos = new ArrayList<>();
      refArgs = new ArrayList<>();
      this.condition = condition;
      int counter = 0;
      for (int i = 0; i < operator.getArguments().size(); i++) {
        Argument arg = operator.getArguments().get(i);
        if (arg.isConstant()) {
          continue;
        }
        int aIdx = condition.getArguments().indexOf(arg);
        if (aIdx >= 0) {
          conditionPos.add(aIdx);
          operatorPos.add(counter);
          refArgs.add(arg);
          size++;
        }
        counter++;
      }
    }

    public int size() {
      return size;
    }

    public int getOperatorIndex() {
      return operatorIndex;
    }

    public int getConditionPos(int i) {
      return conditionPos.get(i);
    }

    public int getOperatorPos(int i) {
      return operatorPos.get(i);
    }

    public List<Argument> getRefArgs() {
      return refArgs;
    }

    public Condition getCondition() {
      return condition;
    }

    private int size;
    private int operatorIndex;
    private List<Argument> refArgs;
    private List<Integer> conditionPos;
    private List<Integer> operatorPos;
    private Condition condition;
  }

  class OperatorParameterList {
    public OperatorParameterList(Operator o) {
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

    public void addOperator(Operator o) {
      for (int i = 0; i < freeParameters.size(); i++) {
        Argument arg = o.getArguments().get(freeParameters.get(i));
        if (!argumentList.get(i).contains(arg)) {
          argumentList.get(i).add(arg);
        }
      }
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
        int operatorPos = mapping.getOperatorPos(i);
        args.add(argumentList.get(operatorPos));
      }
      return args;
    }

    List<List<Argument>> argumentList;
    List<Integer> freeParameters;
  }

  class ArgumentAssignment {
    public ArgumentAssignment(ArgumentMapping mapping, List<Argument> conditionArguments) {
      this.mapping = mapping;
      arguments = new ArrayList<>();
      for (int i = 0; i < mapping.size(); i++) {
        arguments.add(conditionArguments.get(mapping.getConditionPos(i)));
      }
      condition = mapping.getCondition().getConditionBoundToArguments(mapping.getRefArgs(), arguments);
    }

    public int size() {
      return arguments.size();
    }

    public ArgumentMapping getMapping() {
      return mapping;
    }

    public Condition getCondition() {
      return condition;
    }

    List<Argument> getArguments() {
      return arguments;
    }

    private Condition condition;
    private ArgumentMapping mapping;
    private List<Argument> arguments;
  }

  class OperatorLookup {
    public OperatorLookup() {
      posPreconditions = new HashMap<>();
      negPreconditions = new HashMap<>();
      posEffects = new HashMap<>();
      negEffects = new HashMap<>();
    }

    public void addAssignment(ArgumentAssignment assignment, boolean isNegated, boolean isEffect) {
      Condition condition = assignment.getCondition();
      if (isEffect) {
        if (isNegated) {
          negEffects.putIfAbsent(condition, new ArrayList<>());
          negEffects.get(condition).add(assignment);
        } else {
          posEffects.putIfAbsent(condition, new ArrayList<>());
          posEffects.get(condition).add(assignment);
        }
      } else {
        if (isNegated) {
          negPreconditions.putIfAbsent(condition, new ArrayList<>());
          negPreconditions.get(condition).add(assignment);
        } else {
          posPreconditions.putIfAbsent(condition, new ArrayList<>());
          posPreconditions.get(condition).add(assignment);
        }
      }
    }

    public List<ArgumentAssignment> getAssignments(Condition condition, boolean isNegated, boolean isEffect) {
      Condition c = condition.withoutNegation();
      return isNegated
          ? (isEffect ? negEffects.getOrDefault(c, new ArrayList<>())
              : negPreconditions.getOrDefault(c, new ArrayList<>()))
          : (isEffect ? posEffects.getOrDefault(c, new ArrayList<>())
              : posPreconditions.getOrDefault(c, new ArrayList<>()));
    }

    Map<Condition, List<ArgumentAssignment>> posPreconditions;
    Map<Condition, List<ArgumentAssignment>> negPreconditions;
    Map<Condition, List<ArgumentAssignment>> posEffects;
    Map<Condition, List<ArgumentAssignment>> negEffects;
  }

  public List<Boolean> computeGroundArguments(Operator operator, OperatorParameterList args) {
    List<Boolean> result = new ArrayList<>();
    for (int i = 0; i < operator.getArguments().size(); i++) {
      result.add(false);
    }
    return result;
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

  private List<Integer> implyCondition(ArgumentAssignment assignment) {
    int operatorIndex = assignment.getMapping().getOperatorIndex();
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
      if (condition.isNegated() && !initialState.contains(condition)) {
        return SAT;
      } else if (!condition.isNegated() && initialState.contains(condition)) {
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

  public void addParameterImpliesCondition(ArgumentAssignment assignment, Condition condition, boolean isEffect) {
    List<Integer> clause = implyCondition(assignment);
    clause.add(getConditionSatVar(condition, !isEffect));
    System.out.println(clause);
    if (isEffect) {
      encoding.transitionClauses.addClause(clause.stream().mapToInt(x -> x).toArray());
    } else {
      encoding.universalClauses.addClause(clause.stream().mapToInt(x -> x).toArray());
    }
  }

  public void atMostOneParameter() {
    for (int oIdx = 0; oIdx < partiallyGroundedOperators.size(); oIdx++) {
      System.out.println("Operator " + partiallyGroundedOperators.get(oIdx).getName());
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
          System.out.println("Operator -> parameter");
          System.out.println(clause);
        }
        {
          // Parameter -> Operator
          for (int aIdx = 0; aIdx < possibleArguments.get(oIdx).getPossibleArguments(pIdx).size(); aIdx++) {
            int clause[] = new int[2];
            clause[0] = -getParameterSatVar(oIdx, pIdx, aIdx);
            clause[1] = operatorSatVars.get(oIdx);
            encoding.universalClauses.addClause(clause);
            System.out.println("Parameter -> Operator");
            System.out.println(clause);
          }
        }
        // AMO Parameter
        encoding.universalClauses
            .addAtMostOneGroup(parameterSatVars.get(oIdx).get(pIdx).stream().mapToInt(x -> x).toArray());
      }
    }
  }

  public void parametersImplyConditions() {
    operatorLookup = new OperatorLookup();
    for (int oIdx = 0; oIdx < partiallyGroundedOperators.size(); oIdx++) {
      Operator partiallyGroundedOperator = partiallyGroundedOperators.get(oIdx);
      System.out.println("Operator " + partiallyGroundedOperator.getName());
      {
        List<Condition> preconditions = getConditionList(partiallyGroundedOperator.getPrecondition());
        for (Condition condition : preconditions) {
          System.out.println(condition);
          ArgumentMapping mapping = new ArgumentMapping(partiallyGroundedOperator, condition);
          List<List<Argument>> args = possibleArguments.get(oIdx).getPossibleArguments(mapping);
          ArgumentCombinationUtils.Iterator argumentIterator = new ArgumentCombinationUtils.Iterator(args);
          argumentIterator.forEachRemaining(groundedArgs -> {
            Condition groundedCondition = condition.getConditionBoundToArguments(mapping.getRefArgs(), groundedArgs);
            ArgumentAssignment assignment = new ArgumentAssignment(mapping, groundedCondition.getArguments());
            addParameterImpliesCondition(assignment, groundedCondition, false);
            if (conditions.contains(groundedCondition.withoutNegation())) {
              operatorLookup.addAssignment(assignment, groundedCondition.isNegated(), false);
            }
          });
        }
      }
      {
        List<Condition> effects = getConditionList(partiallyGroundedOperator.getEffect());
        for (Condition condition : effects) {
          System.out.println(condition);
          ArgumentMapping mapping = new ArgumentMapping(partiallyGroundedOperator, condition);
          List<List<Argument>> args = possibleArguments.get(oIdx).getPossibleArguments(mapping);
          ArgumentCombinationUtils.Iterator argumentIterator = new ArgumentCombinationUtils.Iterator(args);
          argumentIterator.forEachRemaining(groundedArgs -> {
            Condition groundedCondition = condition.getConditionBoundToArguments(mapping.getRefArgs(), groundedArgs);
            ArgumentAssignment assignment = new ArgumentAssignment(mapping, groundedCondition.getArguments());
            addParameterImpliesCondition(assignment, groundedCondition, true);
            if (conditions.contains(groundedCondition.withoutNegation())) {
              operatorLookup.addAssignment(assignment, groundedCondition.isNegated(), true);
            }
          });
        }
      }
    }
  }

  public void interference() {
    for (Condition condition : conditions) {
      for (ArgumentAssignment preconditionAssignment : operatorLookup.getAssignments(condition, false, false)) {
        for (ArgumentAssignment effectAssignment : operatorLookup.getAssignments(condition, true, true)) {
          if (preconditionAssignment.getMapping().getOperatorIndex() == effectAssignment.getMapping()
              .getOperatorIndex()) {
            continue;
          }
          forbidParameters(preconditionAssignment, effectAssignment);
        }
      }
      for (ArgumentAssignment preconditionAssignment : operatorLookup.getAssignments(condition, true, false)) {
        for (ArgumentAssignment effectAssignment : operatorLookup.getAssignments(condition, false, true)) {
          if (preconditionAssignment.getMapping().getOperatorIndex() == effectAssignment.getMapping()
              .getOperatorIndex()) {
            continue;
          }
          forbidParameters(preconditionAssignment, effectAssignment);
        }
      }
    }
  }

  public void forbidParameters(ArgumentAssignment first, ArgumentAssignment second) {
    List<Integer> clause = new ArrayList<>();
    clause.addAll(implyCondition(first));
    clause.addAll(implyCondition(second));
    encoding.universalClauses.addClause(clause.stream().mapToInt(x -> x).toArray());
  }

  public void frameAxioms() {
    for (Condition condition : conditions) {
      List<int[]> dnf = new ArrayList<>();
      dnf.add(new int[] { getConditionSatVar(condition, true) });
      dnf.add(new int[] { -getConditionSatVar(condition, false) });
      List<ArgumentAssignment> assignmentList = operatorLookup.getAssignments(condition, false, true);
      if (assignmentList.size() == 0) {
        Logger.log(Logger.WARN, "no assignment supports positive condition " + condition);
      }
      for (ArgumentAssignment assignment : assignmentList) {
        int operatorIndex = assignment.getMapping().getOperatorIndex();
        if (assignment.size() == 0) {
          dnf.add(new int[] { operatorSatVars.get(operatorIndex) });
        } else if (assignment.size() == 1) {
          dnf.add(new int[] { getParameterSatVar(operatorIndex, assignment.getMapping().getOperatorPos(0),
              assignment.getArguments().get(0)) });
        } else {
          Logger.log(Logger.WARN, "Assignment has more than one free parameter");
        }
      }
      encoding.transitionClauses.addDNF(dnf);
    }
    for (Condition condition : conditions) {
      List<int[]> dnf = new ArrayList<>();
      dnf.add(new int[] { -getConditionSatVar(condition, true) });
      dnf.add(new int[] { getConditionSatVar(condition, false) });
      List<ArgumentAssignment> assignmentList = operatorLookup.getAssignments(condition, true, true);
      if (assignmentList.size() == 0) {
        Logger.log(Logger.WARN, "no assignment supports negative condition " + condition);
      }
      for (ArgumentAssignment assignment : assignmentList) {
        int operatorIndex = assignment.getMapping().getOperatorIndex();
        if (assignment.size() == 0) {
          dnf.add(new int[] { operatorSatVars.get(operatorIndex) });
        } else if (assignment.size() == 1) {
          dnf.add(new int[] { getParameterSatVar(operatorIndex, assignment.getMapping().getOperatorPos(0),
              assignment.getArguments().get(0)) });
        } else {
          Logger.log(Logger.WARN, "Assignment has more than one free parameter");
        }
      }
      encoding.transitionClauses.addDNF(dnf);
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
    System.out.println("Operator sat vars");
    for (int i = 0; i < partiallyGroundedOperators.size(); i++) {
      System.out.println("Operator " + partiallyGroundedOperators.get(i).getName() + ": " + operatorSatVars.get(i));
      System.out.println(parameterSatVars.get(i));
    }
    System.out.println("Condition sat vars");
    System.out.println(conditionSatVars);
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
    List<List<Boolean>> operatorArgumentsToGround = new ArrayList<>();
    for (Operator o : liftedOperators) {
      int idx = operatorIndex.get(o.getName());
      operatorArgumentsToGround.add(computeGroundArguments(o, operatorArgs.get(idx)));
    }
    partiallyGroundedOperators = new ArrayList<Operator>();
    partiallyGroundedOperatorLookup = new ArrayList<>();
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
      Operator partiallyGroundedOperator = liftedOperator.getOperatorWithGroundArguments(args);
      int lookupIdx = partiallyGroundedOperators.indexOf(partiallyGroundedOperator);
      if (lookupIdx == -1) {
        lookupIdx = partiallyGroundedOperators.size();
        partiallyGroundedOperators.add(partiallyGroundedOperator);
      }
      partiallyGroundedOperatorLookup.add(lookupIdx);
    }
  }

  @Override
  public OperatorPlan plan(PlanningProblem problem) {
    initialState = new HashSet<>();
    initialState.addAll(problem.getInitialState());
    System.out.println("Initial problem");
    System.out.println(problem);
    grounder = new PlanningGraphGrounder(config);
    GroundPlanningProblem groundedProblem = grounder.ground(problem);
    goal = new ArrayList<>();
    for (AbstractCondition abstractCondition : problem.getGoals()) {
      goal.addAll(getConditionList(abstractCondition));
    }
    setPartiallyGroundedOperators(problem.getOperators(), grounder.getFilteredActions());
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
    System.out.println("Partially grounded operators");
    System.out.println(partiallyGroundedOperators);
    conditions = new ArrayList<>(conditionSet);
    System.out.println("All conditions");
    System.out.println(conditions);

    initializeSatIds();
    encoding = new SymbolicReachabilityFormula();
    encoding.universalClauses = new SatFormula(numVars);
    encoding.transitionClauses = new SatFormula(numVars);
    encoding.universalClauses.addClause(new int[] { SAT });
    atMostOneParameter();
    // parametersImplyConditions();
    // interference();
    // frameAxioms();
    initialState();
    goal();
    SymbolicReachabilitySolver solver = new SymbolicReachabilitySolver(new IpasirSatSolver());
    List<int[]> model = solver.solve(encoding);
    System.out.println(model);
    OperatorPlan plan = extractPlan(model);
    System.out.println("Done planning");
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
          plan.appendAtBack(groundedOperator);
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
  private OperatorLookup operatorLookup;

  private SymbolicReachabilityFormula encoding;
  // private List<List<List<Argument>>> eligibleArgumentCombinations;
  private List<OperatorParameterList> possibleArguments;
  private List<Integer> operatorSatVars;
  private List<List<List<Integer>>> parameterSatVars;
  private List<Integer> conditionSatVars;
  private int numVars;

  private List<Operator> partiallyGroundedOperators;
  private List<Condition> conditions;

}
