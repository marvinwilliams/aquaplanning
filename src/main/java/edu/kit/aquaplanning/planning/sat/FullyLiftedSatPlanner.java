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
import edu.kit.aquaplanning.sat.IpasirSatSolver;
import edu.kit.aquaplanning.sat.SatFormula;
import edu.kit.aquaplanning.sat.SymbolicReachabilityFormula;
import edu.kit.aquaplanning.sat.SymbolicReachabilitySolver;
import edu.kit.aquaplanning.util.Logger;
import edu.kit.aquaplanning.util.Pair;

public class FullyLiftedSatPlanner extends LiftedPlanner {
  public FullyLiftedSatPlanner(Configuration config) {
    super(config);
  }

  // parameterIndex is free index
  private int getArgumentIndex(int operatorIndex, int parameterIndex, Argument argument) {
    return possibleArguments.get(operatorIndex).get(parameterIndex).indexOf(argument);
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
    picClauses++;
  }

  public void atMostOneParameter() {
    for (int oIdx = 0; oIdx < operators.size(); oIdx++) {
      // System.out.println("Operator " +
      // partiallyGroundedOperators.get(oIdx).getName());
      for (int pIdx = 0; pIdx < possibleArguments.get(oIdx).size(); pIdx++) {
        {
          // Operator -> Parameter
          int clause[] = new int[possibleArguments.get(oIdx).get(pIdx).size() + 1];
          int counter = 0;
          clause[counter++] = -operatorSatVars.get(oIdx);
          for (int aIdx = 0; aIdx < possibleArguments.get(oIdx).get(pIdx).size(); aIdx++) {
            clause[counter++] = getParameterSatVar(oIdx, pIdx, aIdx);
          }
          encoding.universalClauses.addClause(clause);
          amopClauses++;
          // System.out.println("Operator -> parameter");
          // System.out.println(Arrays.toString(clause));
        }
        {
          // Parameter -> Operator
          for (int aIdx = 0; aIdx < possibleArguments.get(oIdx).get(pIdx).size(); aIdx++) {
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
    for (int oIdx = 0; oIdx < operators.size(); oIdx++) {
      Operator operator = operators.get(oIdx);
      // System.out.println("Operator " + partiallyGroundedOperator.getName());
      {
        List<Condition> preconditions = getConditionList(operator.getPrecondition());
        for (Condition condition : preconditions) {
          // System.out.println(condition);
          LiftedSatUtils.ArgumentMapping mapping = new LiftedSatUtils.ArgumentMapping(operator, condition);
          List<List<Argument>> args = new ArrayList<>();
          for (int i = 0; i < mapping.size(); i++) {
            args.add(possibleArguments.get(oIdx).get(mapping.getOperatorPos(i)));
          }
          ArgumentCombinationUtils.Iterator argumentIterator = new ArgumentCombinationUtils.Iterator(args);
          argumentIterator.forEachRemaining(groundedArgs -> {
            Condition groundedCondition = condition.getConditionBoundToArguments(mapping.getRefArgs(), groundedArgs);
            LiftedSatUtils.ArgumentAssignment assignment = new LiftedSatUtils.ArgumentAssignment(mapping,
                groundedCondition.getArguments());
            addParameterImpliesCondition(assignment, groundedCondition, false);
            conditionSupport.addAssignment(assignment, groundedCondition.isNegated(), false);
          });
        }
      }
      {
        List<Condition> effects = getConditionList(operator.getEffect());
        for (Condition condition : effects) {
          // System.out.println(condition);
          LiftedSatUtils.ArgumentMapping mapping = new LiftedSatUtils.ArgumentMapping(operator, condition);
          List<List<Argument>> args = new ArrayList<>();
          for (int i = 0; i < mapping.size(); i++) {
            args.add(possibleArguments.get(oIdx).get(mapping.getOperatorPos(i)));
          }
          ArgumentCombinationUtils.Iterator argumentIterator = new ArgumentCombinationUtils.Iterator(args);
          argumentIterator.forEachRemaining(groundedArgs -> {
            Condition groundedCondition = condition.getConditionBoundToArguments(mapping.getRefArgs(), groundedArgs);
            LiftedSatUtils.ArgumentAssignment assignment = new LiftedSatUtils.ArgumentAssignment(mapping,
                groundedCondition.getArguments());
            addParameterImpliesCondition(assignment, groundedCondition, true);
            conditionSupport.addAssignment(assignment, groundedCondition.isNegated(), true);
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
    ifrClauses++;
  }

  public void frameAxiomCondition(Condition condition, boolean isNegated) {
    List<int[]> dnf = new ArrayList<>();
    dnf.add(new int[] { (isNegated ? -1 : 1) * getConditionSatVar(condition, true) });
    dnf.add(new int[] { (isNegated ? 1 : -1) * getConditionSatVar(condition, false) });
    List<LiftedSatUtils.ArgumentAssignment> assignmentList = conditionSupport.getAssignments(condition, isNegated,
        true);
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
    for (int oIdx = 0; oIdx < operators.size(); oIdx++) {
      operatorSatVars.add(satVar++);
      parameterSatVars.add(new ArrayList<>());
      for (int pIdx = 0; pIdx < possibleArguments.get(oIdx).size(); pIdx++) {
        parameterSatVars.get(oIdx).add(new ArrayList<>());
        for (int k = 0; k < possibleArguments.get(oIdx).get(pIdx).size(); k++) {
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

  @Override
  public OperatorPlan plan(PlanningProblem problem) {
    Logger.log(Logger.INFO, "TIME_INIT");
    this.problem = problem;
    System.out.println(problem);
    grounder = new PlanningGraphGrounder(config);
    initialState = new HashSet<>();
    initialState.addAll(problem.getInitialState());
    operators = problem.getOperators();
    operatorIndexMap = new HashMap<>();
    for (Operator o: operators) {
      operatorIndexMap.put(o, operatorIndexMap.size());
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
    System.out.println("Init: " + initialState);
    System.out.println("Goal: " + goal);
    Logger.log(Logger.INFO, "TIME_PART");

    conditions = new ArrayList<>();
    Map<Type, List<Argument>> constantsOfType = new HashMap<>();
    for (Predicate p : problem.getPredicates().values()) {
      List<List<Argument>> args = new ArrayList<>();
      for (Type t : p.getArgumentTypes()) {
        if (!constantsOfType.containsKey(t)) {
          List<Argument> argList = new ArrayList<>();
          for (Argument arg : problem.getConstants()) {
            if (problem.isArgumentOfType(arg, t)) {
              argList.add(arg);
            }
          }
          constantsOfType.put(t, argList);
        }
        args.add(constantsOfType.get(t));
      }
      ArgumentCombinationUtils.Iterator argumentIterator = new ArgumentCombinationUtils.Iterator(args);
      argumentIterator.forEachRemaining(groundedArgs -> {
        Condition condition = new Condition(p);
        for (Argument a : groundedArgs) {
          condition.addArgument(a);
        }
        conditions.add(condition);
      });
    }
    System.out.println("Conditions: " + conditions);
    // System.out.println("Partially grounded");
    // System.out.println(partiallyGroundedOperators);
    // eligibleArgumentCombinations = new ArrayList<>();
    possibleArguments = new ArrayList<>();
    // Setup the relevant operators for lookup
    for (Operator o : operators) {
      List<List<Argument>> paramList = new ArrayList<>();
      for (Type t : o.getArgumentTypes()) {
        if (!constantsOfType.containsKey(t)) {
          List<Argument> argList = new ArrayList<>();
          for (Argument arg : problem.getConstants()) {
            if (problem.isArgumentOfType(arg, t)) {
              argList.add(arg);
            }
          }
          constantsOfType.put(t, argList);
        }
        paramList.add(constantsOfType.get(t));
      }
      possibleArguments.add(paramList);
    }
    System.out.println(possibleArguments);
    // Iterate over all operators to collect parameter information and conditions
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
      for (int oIdx = 0; oIdx < operators.size(); oIdx++) {
        Operator operator = operators.get(oIdx);
        if (model.get(i)[operatorSatVars.get(oIdx)] > 0) {
          List<Argument> args = new ArrayList<>();
          for (int pos = 0; pos < operator.getArguments().size(); pos++) {
            args.add(null);
          }
          for (int j = 0; j < possibleArguments.get(oIdx).size(); j++) {
            boolean found = false;
            for (Argument arg : possibleArguments.get(oIdx).get(j)) {
              if (model.get(i)[getParameterSatVar(oIdx, j, arg)] >= 0) {
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
  private LiftedSatUtils.ConditionSupport conditionSupport;
  private int amopClauses;
  private int picClauses;
  private int ifrClauses;
  private int frameClauses;

  private SymbolicReachabilityFormula encoding;
  private List<List<List<Argument>>> possibleArguments;
  private List<Integer> operatorSatVars;
  private List<List<List<Integer>>> parameterSatVars;
  private List<Integer> conditionSatVars;
  private int numVars;

  private List<Operator> operators;
  private Map<Operator, Integer> operatorIndexMap;
  private List<Condition> conditions;
}
