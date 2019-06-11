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
import edu.kit.aquaplanning.model.ground.ActionPlan;
import edu.kit.aquaplanning.model.ground.GroundPlanningProblem;
import edu.kit.aquaplanning.model.lifted.Argument;
import edu.kit.aquaplanning.model.lifted.Operator;
import edu.kit.aquaplanning.model.lifted.PlanningProblem;
import edu.kit.aquaplanning.model.lifted.condition.AbstractCondition;
import edu.kit.aquaplanning.model.lifted.condition.AbstractCondition.ConditionType;
import edu.kit.aquaplanning.model.lifted.condition.Condition;
import edu.kit.aquaplanning.model.lifted.condition.ConditionSet;
import edu.kit.aquaplanning.planning.LiftedPlanner;
import edu.kit.aquaplanning.sat.SatFormula;
import edu.kit.aquaplanning.sat.SymbolicReachabilityFormula;
import edu.kit.aquaplanning.util.Logger;
import edu.kit.aquaplanning.util.Pair;

public class LiftedSatPlanner extends LiftedPlanner {
  class ArgumentMapping {
    public ArgumentMapping(Operator operator, Condition condition) {
      operatorIndex = partiallyGroundedOperators.indexOf(operator);
      init(operator, condition);
    }

    public ArgumentMapping(int operatorIndex, Condition condition) {
      this.operatorIndex = operatorIndex;
      Operator o = partiallyGroundedOperators.get(operatorIndex);
      init(o, condition);
    }

    protected void init(Operator operator, Condition condition) {
      size = 0;
      conditionPos = new ArrayList<>();
      operatorPos = new ArrayList<>();
      refArgs = new ArrayList<>();
      this.condition = condition;
      for (int i = 0; i < condition.getNumArgs(); i++) {
        Argument arg = condition.getArguments().get(i);
        int aIdx = arg.isConstant() ? -1 : operator.getArguments().indexOf(condition.getArguments().get(i));
        if (aIdx >= 0) {
          conditionPos.add(i);
          operatorPos.add(aIdx);
          refArgs.add(arg);
          size++;
        }
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
      possibleArguments = new ArrayList<>();
      while (possibleArguments.size() < freeParameters.size()) {
        possibleArguments.add(new ArrayList<>());
      }
    }

    public void addOperator(Operator o) {
      for (int i = 0; i < freeParameters.size(); i++) {
        Argument arg = o.getArguments().get(freeParameters.get(i));
        if (!possibleArguments.get(i).contains(arg)) {
          possibleArguments.get(i).add(arg);
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
      return possibleArguments.get(i);
    }

    public List<List<Argument>> getPossibleArguments(ArgumentMapping mapping) {
      List<List<Argument>> args = new ArrayList<>();
      for (int i = 0; i < mapping.size(); i++) {
        int operatorPos = mapping.getOperatorPos(i);
        args.add(possibleArguments.get(operatorPos));
      }
      return args;
    }

    List<List<Argument>> possibleArguments;
    List<Integer> freeParameters;
  }

  class ArgumentAssignment {
    public ArgumentAssignment(ArgumentMapping mapping, List<Argument> conditionArguments) {
      this.mapping = mapping;
      arguments = new ArrayList<>();
      for (int i = 0; i < mapping.size(); i++) {
        arguments.add(conditionArguments.get(mapping.getConditionPos(i)));
      }
      condition = mapping.getCondition().getConditionBoundToArguments(mapping.getRefArgs(), conditionArguments);
    }

    public int size() {
      return arguments.size();
    }

    public ArgumentMapping getMapping() {
      return mapping;
    }

    public Argument getArgument(int i) {
      return arguments.get(i);
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

    public void addAssignment(ArgumentAssignment assignment, boolean isPositive, boolean isEffect) {
      Condition condition = assignment.getCondition().withoutNegation();
      if (isEffect) {
        if (isPositive) {
          posEffects.putIfAbsent(condition, new ArrayList<>());
          posEffects.get(condition).add(assignment);
        } else {
          negEffects.putIfAbsent(condition, new ArrayList<>());
          negEffects.get(condition).add(assignment);
        }
      } else {
        if (isPositive) {
          posPreconditions.putIfAbsent(condition, new ArrayList<>());
          posPreconditions.get(condition).add(assignment);
        } else {
          negPreconditions.putIfAbsent(condition, new ArrayList<>());
          negPreconditions.get(condition).add(assignment);
        }
      }
    }

    public List<ArgumentAssignment> getAssignments(Condition condition, boolean isPositive, boolean isEffect) {
      return isPositive
          ? (isEffect ? posEffects.getOrDefault(condition, new ArrayList<>())
              : posPreconditions.getOrDefault(condition, new ArrayList<>()))
          : (isEffect ? negEffects.getOrDefault(condition, new ArrayList<>())
              : negPreconditions.getOrDefault(condition, new ArrayList<>()));
    }

    Map<Condition, List<ArgumentAssignment>> posPreconditions;
    Map<Condition, List<ArgumentAssignment>> negPreconditions;
    Map<Condition, List<ArgumentAssignment>> posEffects;
    Map<Condition, List<ArgumentAssignment>> negEffects;
  }

  public LiftedSatPlanner(Configuration config) {
    super(config);
  }

  public List<Boolean> computeGroundArguments(Operator operator, OperatorParameterList args) {
    List<Boolean> result = new ArrayList<>();
    for (int i = 0; i < operator.getArguments().size(); i++) {
      result.add(false);
    }
    return result;
  }

  private int getArgumentIndex(int operatorIndex, int parameterIndex, Argument argument) {
    return possibleArguments.get(operatorIndex).getPossibleArguments(parameterIndex).indexOf(argument);
  }

  private int getParameterSatVar(int operatorIndex, int parameterIndex, Argument argument) {
    int argumentIndex = getArgumentIndex(operatorIndex, parameterIndex, argument);
    return parameterSatVars.get(operatorIndex).get(parameterIndex).get(argumentIndex);
  }

  private List<Integer> implyCondition(ArgumentAssignment assignment) {
    int operatorIndex = assignment.getMapping().getOperatorIndex();
    List<Integer> clause = new ArrayList<>();
    clause.add(-operatorSatVars.get(operatorIndex));
    for (int i = 0; i < assignment.size(); i++) {
      clause.add(
          -getParameterSatVar(operatorIndex, assignment.getMapping().getOperatorPos(i), assignment.getArgument(i)));
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

  public void addParameterImpliesCondition(ArgumentAssignment assignment, boolean isEffect) {
    List<Integer> clause = implyCondition(assignment);
    clause.add(getConditionSatVar(assignment.getMapping().getCondition(), !isEffect));
    if (isEffect) {
      encoding.transitionClauses.addClause(clause.stream().mapToInt(x -> x).toArray());
    } else {
      encoding.universalClauses.addClause(clause.stream().mapToInt(x -> x).toArray());
    }
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
        partiallyGroundedOperators.add(liftedOperator.getOperatorWithGroundArguments(args));
      }
      partiallyGroundedOperatorLookup.add(lookupIdx);
    }
  }

  public void initializeSatIds() {
    // SAT variable
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
    numVars = satVar - 1;
    encoding = new SymbolicReachabilityFormula();
    encoding.universalClauses = new SatFormula(numVars);
    encoding.transitionClauses = new SatFormula(numVars);
  }

  public void atMostOneParameter() {
    for (int oIdx = 0; oIdx < partiallyGroundedOperators.size(); oIdx++) {
      for (int pIdx = 0; pIdx < possibleArguments.get(oIdx).numFreeParameters(); pIdx++) {
        {
          // Operator -> Parameter
          int clause[] = new int[possibleArguments.get(oIdx).getPossibleArguments(pIdx).size() + 1];
          int counter = 0;
          clause[counter++] = -operatorSatVars.get(oIdx);
          for (int aIdx = 0; aIdx < possibleArguments.get(oIdx).getPossibleArguments(pIdx).size(); aIdx++) {
            clause[counter++] = getParameterSatVar(oIdx, pIdx,
                possibleArguments.get(oIdx).getPossibleArguments(pIdx).get(aIdx));
          }
          encoding.universalClauses.addClause(clause);
        }
        {
          // Parameter -> Operator
          for (int aIdx = 0; aIdx < possibleArguments.get(oIdx).getPossibleArguments(pIdx).size(); aIdx++) {
            int clause[] = new int[2];
            clause[0] = -getParameterSatVar(oIdx, pIdx,
                possibleArguments.get(oIdx).getPossibleArguments(pIdx).get(aIdx));
            clause[1] = operatorSatVars.get(oIdx);
            encoding.universalClauses.addClause(clause);
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
      {
        List<Condition> preconditions = getConditionList(partiallyGroundedOperator.getPrecondition());
        for (Condition condition : preconditions) {
          ArgumentMapping mapping = new ArgumentMapping(partiallyGroundedOperator, condition);
          List<List<Argument>> args = possibleArguments.get(oIdx).getPossibleArguments(mapping);
          ArgumentCombinationUtils.Iterator argumentIterator = new ArgumentCombinationUtils.Iterator(args);
          argumentIterator.forEachRemaining(groundedArgs -> {
            Condition groundedCondition = condition.getConditionBoundToArguments(mapping.getRefArgs(), groundedArgs);
            ArgumentAssignment assignment = new ArgumentAssignment(mapping, groundedCondition.getArguments());
            addParameterImpliesCondition(assignment, false);
            operatorLookup.addAssignment(assignment, false);
          });
        }
      }
      {
        List<Condition> effects = getConditionList(partiallyGroundedOperator.getEffect());
        for (Condition condition : effects) {
          ArgumentMapping mapping = new ArgumentMapping(partiallyGroundedOperator, condition);
          List<List<Argument>> args = possibleArguments.get(oIdx).getPossibleArguments(mapping);
          ArgumentCombinationUtils.Iterator argumentIterator = new ArgumentCombinationUtils.Iterator(args);
          argumentIterator.forEachRemaining(groundedArgs -> {
            Condition groundedCondition = condition.getConditionBoundToArguments(mapping.getRefArgs(), groundedArgs);
            ArgumentAssignment assignment = new ArgumentAssignment(mapping, groundedCondition.getArguments());
            addParameterImpliesCondition(assignment, true);
            operatorLookup.addAssignment(assignment, true);
          });
        }
      }
    }
  }

  public void forbidParameters(ArgumentAssignment first, ArgumentAssignment second) {

  }

  public void interference() {
    for (Condition condition : conditions) {
      for (ArgumentAssignment preconditionAssignment : operatorLookup.getAssignments(condition, condition.isNegated(),
          false)) {
        for (ArgumentAssignment effectAssignment : operatorLookup.getAssignments(condition, !condition.isNegated(),
            true)) {
          // TODO
        }
      }
    }
  }

  // if(precondition.withoutNegation().equals(effect.withoutNegation())&&precondition.isNegated()!=effect.isNegated())

  // {
  // forbidParameters(assignment, otherAssignment);
  // }

  @Override
  public ActionPlan plan(PlanningProblem problem) {
    initialState = new HashSet<>();
    initialState.addAll(problem.getInitialState());
    grounder = new PlanningGraphGrounder(config);
    GroundPlanningProblem groundedProblem = grounder.ground(problem);
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
    conditions = new ArrayList<>(conditionSet);
    initializeSatIds();
    encoding = new SymbolicReachabilityFormula();
    encoding.universalClauses = new SatFormula(numVars);
    encoding.transitionClauses = new SatFormula(numVars);
    encoding.universalClauses.addClause(new int[] { SAT });
    atMostOneParameter();
    parametersImplyConditions();
    interference();
    System.out.println("Done planning");
    return null;
  }

  private static int SAT = 1;
  private Set<Condition> initialState;
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
