package edu.kit.aquaplanning.planning;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.function.BiPredicate;
import java.util.stream.Collectors;

import edu.kit.aquaplanning.Configuration;
import edu.kit.aquaplanning.grounding.Preprocessor;
import edu.kit.aquaplanning.grounding.RelaxedPlanningGraphGrounder;
import edu.kit.aquaplanning.model.ground.Plan;
import edu.kit.aquaplanning.model.lifted.Argument;
import edu.kit.aquaplanning.model.lifted.Operator;
import edu.kit.aquaplanning.model.lifted.PlanningProblem;
import edu.kit.aquaplanning.model.lifted.Predicate;
import edu.kit.aquaplanning.model.lifted.Type;
import edu.kit.aquaplanning.model.lifted.condition.AbstractCondition;
import edu.kit.aquaplanning.model.lifted.condition.AbstractCondition.ConditionType;
import edu.kit.aquaplanning.model.lifted.condition.Condition;
import edu.kit.aquaplanning.model.lifted.condition.ConditionSet;
import edu.kit.aquaplanning.sat.SatSolver;
import edu.kit.aquaplanning.util.Pair;

public class PureLiftedSatPlanner extends LiftedPlanner {

  public PureLiftedSatPlanner(Configuration config) {
    super(config);
  }

  @Override
  public Plan findPlan(PlanningProblem p) {
    problem = p;
    new Preprocessor(config).preprocess(problem);
    isGrounded = (o, a) -> a.getName().startsWith("?x");
    setIDs();
    generateClauses();
    // initialize the SAT solver
    SatSolver solver = new SatSolver();

    int step = 0;

    for (int[] clause : initialClauses) {
      solver.addClause(clause);
    }
    while (true) {
      if (solver.isSatisfiable(goal)) {
        System.out.println("Solution found in step " + step);
        break;
      }
      System.out.println("No solution found in step " + step);
      for (int[] clause : universalClauses) {
        solver.addClause(clause);
      }
      for (int[] clause : transitionClauses) {
        solver.addClause(clause);
      }
      nextStep();
      step++;
    }
    // Decode the plan
    Plan plan = new Plan();
    RelaxedPlanningGraphGrounder grounder = new RelaxedPlanningGraphGrounder(config);
    grounder.ground(problem);
    int[] model = solver.getModel();
    for (int s = 0; s < step; s++) {
      for (int i = 0; i < operators.size(); i++) {
        if (model[getOperatorNr(i) + s * stepVars] > 0) {
          Operator o = operators.get(i);
          System.out.println("Original Operator: " + operators.get(i));
          System.out.print("Apply action " + i + " with");
          List<Argument> args = new ArrayList<>();
          for (int j = 0; j < o.getArguments().size(); j++) {
            Argument a = o.getArguments().get(j);
            boolean found = getConstantsOfType(a.getType()).size() == 0;
            for (int k = 0; k < getConstantsOfType(a.getType()).size(); k++) {
              if (model[getParameterId(i, j, constantId.get(getConstantsOfType(a.getType()).get(k)))
                  + s * stepVars] >= 0) {
                args.add(getConstantsOfType(a.getType()).get(k));
                System.out.print(" " + j + ": " + getConstantsOfType(a.getType()).get(k));
                found = true;
                break;
              }
            }
            if (!found) {
              System.out.println("ERROR: no parameter set in solution");
              System.exit(1);
            }
          }
          System.out.println("");
          Operator go = o.getOperatorWithGroundArguments(args);
          System.out.println("New operator: " + go);
          System.out.println(grounder.getAction(go));
          plan.appendAtBack(grounder.getAction(go));
        }
      }
    }
    return plan;
  }

  protected Set<Condition> groundCondition(Condition condition) {
    Set<Condition> result = new HashSet<>();
    Stack<List<Argument>> work = new Stack<>();
    int numParameters = condition.getNumArgs();
    work.push(new ArrayList<>(condition.getArguments()));
    while (!work.isEmpty()) {
      List<Argument> first = work.pop();
      int pos = -1;
      for (int i = 0; i < numParameters; i++) {
        if (!first.get(i).isConstant()) {
          pos = i;
          break;
        }
      }
      if (pos == -1) {
        Condition c = condition.copy();
        for (int i = 0; i < numParameters; i++) {
          c.getArguments().set(i, first.get(i));
        }
        result.add(c);
      } else {
        for (Argument a : getConstantsOfType(first.get(pos).getType())) {
          List<Argument> newList = new ArrayList<>(first);
          newList.set(pos, a);
          work.push(newList);
        }
      }
    }
    return result;
  }

  protected Set<Operator> groundOperator(Operator operator) {
    Set<Operator> result = new HashSet<>();
    Stack<List<Argument>> work = new Stack<>();
    int numParameters = operator.getArguments().size();
    work.push(Arrays.asList(new Argument[numParameters]));
    List<Integer> positions = new ArrayList<>();
    List<List<Argument>> groundArguments = new ArrayList<>();
    for (int i = 0; i < numParameters; i++) {
      if (isGrounded.test(operator, operator.getArguments().get(i))) {
        positions.add(i);
        groundArguments.add(getConstantsOfType(operator.getArguments().get(i).getType()));
      }
    }
    while (!work.isEmpty()) {
      List<Argument> first = work.pop();
      int pos = -1;
      for (int i = 0; i < positions.size(); i++) {
        if (first.get(positions.get(i)) == null) {
          pos = i;
          break;
        }
      }
      if (pos == -1) {
        Operator o = operator.getOperatorWithGroundArguments(first);
        o.removeConstantArguments();
        result.add(o);
      } else {
        for (Argument a : groundArguments.get(pos)) {
          List<Argument> newList = new ArrayList<>(first);
          newList.set(positions.get(pos), a);
          work.push(newList);
        }
      }
    }
    return result;
  }

  protected void setIDs() {
    stepVars = 0;

    types = new ArrayList<>();
    typeId = new HashMap<>();
    constants = new ArrayList<>();
    constantId = new HashMap<>();
    constantsOfType = new HashMap<>();
    System.out.println("Types:");
    for (Argument a : problem.getConstants()) {
      if (!typeId.containsKey(a.getType())) {
        System.out.println(a.getType() + ": " + types.size());
        typeId.put(a.getType(), types.size());
        types.add(a.getType());
        constantsOfType.put(a.getType(), new ArrayList<>());
      }
      constantId.put(a, constants.size());
      constants.add(a);
      constantsOfType.get(a.getType()).add(a);
    }
    System.out.println("Constants:");
    System.out.println(constants);

    predicates = new ArrayList<>();
    predicateId = new HashMap<>();
    preconditions = new ArrayList<>();
    effects = new ArrayList<>();
    for (Predicate p : problem.getPredicates().values()) {
      System.out.println("Lifted Predicate:" + p);
      Condition condition = new Condition(p);
      for (int i = 0; i < p.getNumArgs(); i++) {
        condition.addArgument(new Argument("?" + String.valueOf(i), p.getArgumentTypes().get(i)));
      }
      System.out.print("\tGrounded:");
      for (Condition c : groundCondition(condition)) {
        System.out.print(" " + c);
        int pNr = predicates.size();
        predicates.add(c);
        predicateId.put(c, pNr);
        Condition neg = c.withoutNegation();
        neg.setNegated(true);
        predicateId.put(neg, pNr);
        preconditions.add(new ArrayList<>());
        preconditions.add(new ArrayList<>());
        effects.add(new ArrayList<>());
        effects.add(new ArrayList<>());
        stepVars++;
      }
      System.out.println("");
    }

    operators = new ArrayList<>();
    operatorId = new HashMap<>();
    operatorParameters = new ArrayList<>();
    for (Operator operator : problem.getOperators()) {
      System.out.println("Lifted Operator:");
      System.out.println(operator);
      Set<Operator> groundedOperators = groundOperator(operator);
      for (Operator o : groundOperator(operator)) {
        int oNr = operatorId.size();
        System.out.println("Grounded Operator:");
        System.out.println(o);
        operators.add(o);
        operatorId.put(o, oNr);
        int numParameters = o.getArguments().stream().mapToInt(a -> getConstantsOfType(a.getType()).size()).sum();
        operatorParameters.add(numParameters);
        stepVars += numParameters;
        List<Condition> flatPreconditions = getFlatConditions(o.getPrecondition());
        {
          for (Condition c : flatPreconditions) {
            System.out.println("\tPrecondition " + c);
            List<Pair<Integer, Integer>> paramList = getParamList(oNr, c);
            System.out.println("\t\tParameter mapping: " + paramList);
            for (Condition gc : groundCondition(c)) {
              if (predicateId.containsKey(gc)) {
                preconditions.get(predicateId.get(gc) * 2 + (gc.isNegated() ? 1 : 0)).add(new Pair<>(oNr, paramList));
              } else {
                System.out.println("ERROR: Precondition not in list");
                System.exit(1);
              }
            }
          }
        }
        {
          List<Condition> flatEffects = getFlatConditions(o.getEffect());
          for (Condition c : flatEffects) {
            System.out.println("\tEffect " + c);
            List<Pair<Integer, Integer>> paramList = getParamList(oNr, c);
            System.out.println("\t\tParameter mapping: " + paramList);
            for (Condition gc : groundCondition(c)) {
              if (predicateId.containsKey(gc)) {
                effects.get(predicateId.get(gc) * 2 + (gc.isNegated() ? 1 : 0)).add(new Pair<>(oNr, paramList));
              } else {
                System.out.println("ERROR: Effect not in list");
                System.exit(1);
              }
            }
          }
        }
      }
      stepVars += groundedOperators.size();
    }
    System.out.println("Grounded Operators:");
    System.out.println(operators);

    System.out.println("Preconditions: " + preconditions);
    System.out.println("Effects: " + effects);
  }

  protected void generateClauses() {
    setInitialState();
    setGoal();
    universalClauses = new ArrayList<>();
    transitionClauses = new ArrayList<>();
    for (int oNr = 0; oNr < operators.size(); oNr++) {
      Operator operator = operators.get(oNr);
      System.out.println("Operator " + oNr);
      for (int pos = 0; pos < operator.getArguments().size(); pos++) {
        Argument argument = operator.getArguments().get(pos);
        List<Argument> argumentConstants = getConstantsOfType(argument.getType());
        {
          // Operator -> each parameter
          System.out.print("\timplies " + argument + ": ");
          int[] clause = new int[argumentConstants.size() + 1];
          clause[0] = -getOperatorNr(oNr);
          for (int cNr = 0; cNr < argumentConstants.size(); cNr++) {
            clause[cNr + 1] = getParameterId(oNr, pos, constantId.get(argumentConstants.get(cNr)));
          }
          universalClauses.add(clause);
        }
        {
          // <=1 per Parameter
          System.out.print("\tAM1 " + argument + ": ");
          for (int c1 = 0; c1 < argumentConstants.size(); c1++) {
            for (int c2 = c1 + 1; c2 < argumentConstants.size(); c2++) {
              int[] clause = new int[2];
              clause[0] = -getParameterId(oNr, pos, constantId.get(argumentConstants.get(c1)));
              clause[1] = -getParameterId(oNr, pos, constantId.get(argumentConstants.get(c2)));
              universalClauses.add(clause);
            }
          }
        }
      }
    }
    for (int pNr = 0; pNr < predicates.size(); pNr++) {
      Condition predicate = predicates.get(pNr);
      // positive
      for (Pair<Integer, List<Pair<Integer, Integer>>> pair : preconditions.get(pNr * 2)) {
        int oNr = pair.getLeft();
        List<Pair<Integer, Integer>> paramList = pair.getRight();
        {
          // action implies precondition
          System.out.print("Operator " + oNr + " has positive precondition " + predicate + ": ");
          int[] clause = new int[2 + paramList.size()];
          int i = 0;
          clause[i++] = -getOperatorNr(oNr);
          for (Pair<Integer, Integer> paramPos : paramList) {
            Argument a = predicate.getArguments().get(paramPos.getLeft());
            clause[i++] = -getParameterId(oNr, paramPos.getRight(), constantId.get(a));
          }
          clause[i++] = getPredicateNr(pNr, false);
          universalClauses.add(clause);
        }
      }
      // negative
      for (Pair<Integer, List<Pair<Integer, Integer>>> pair : preconditions.get(pNr * 2 + 1)) {
        int oNr = pair.getLeft();
        List<Pair<Integer, Integer>> paramList = pair.getRight();
        {
          // action implies precondition
          System.out.print("Operator " + oNr + " has positive precondition " + predicate + ": ");
          int[] clause = new int[2 + paramList.size()];
          int i = 0;
          clause[i++] = -getOperatorNr(oNr);
          for (Pair<Integer, Integer> paramPos : paramList) {
            Argument a = predicate.getArguments().get(paramPos.getLeft());
            clause[i++] = -getParameterId(oNr, paramPos.getRight(), constantId.get(a));
          }
          clause[i++] = -getPredicateNr(pNr, false);
          universalClauses.add(clause);
        }
      }

      // positive
      for (Pair<Integer, List<Pair<Integer, Integer>>> pair : effects.get(pNr * 2)) {
        int oNr = pair.getLeft();
        List<Pair<Integer, Integer>> paramList = pair.getRight();
        {
          // action implies effect
          System.out.print("Operator " + oNr + " has positive effect " + predicate + ": ");
          int[] clause = new int[2 + paramList.size()];
          int i = 0;
          clause[i++] = -getOperatorNr(oNr);
          for (Pair<Integer, Integer> paramPos : paramList) {
            Argument a = predicate.getArguments().get(paramPos.getLeft());
            clause[i++] = -getParameterId(oNr, paramPos.getRight(), constantId.get(a));
          }
          clause[i++] = getPredicateNr(pNr, true);
          transitionClauses.add(clause);
        }
      }
      // negative
      for (Pair<Integer, List<Pair<Integer, Integer>>> pair : effects.get(pNr * 2 + 1)) {
        int oNr = pair.getLeft();
        List<Pair<Integer, Integer>> paramList = pair.getRight();
        {
          // action implies effect
          System.out.print("Operator " + oNr + " has negative effect " + predicate + ": ");
          int[] clause = new int[2 + paramList.size()];
          int i = 0;
          clause[i++] = -getOperatorNr(oNr);
          for (Pair<Integer, Integer> paramPos : paramList) {
            Argument a = predicate.getArguments().get(paramPos.getLeft());
            clause[i++] = -getParameterId(oNr, paramPos.getRight(), constantId.get(a));
          }
          clause[i++] = -getPredicateNr(pNr, true);
          transitionClauses.add(clause);
        }
      }
      // prevent interference
      for (Pair<Integer, List<Pair<Integer, Integer>>> pair : effects.get(pNr * 2)) {
        int oNr = pair.getLeft();
        List<Pair<Integer, Integer>> paramList = pair.getRight();
        for (Pair<Integer, List<Pair<Integer, Integer>>> pair2 : preconditions.get(pNr * 2 + 1)) {
          int oNr2 = pair2.getLeft();
          if (oNr == oNr2) {
            continue;
          }
          List<Pair<Integer, Integer>> paramList2 = pair2.getRight();
          System.out.print("Operators " + oNr + " and " + oNr2 + " interfere on " + predicate);
          int[] clause = new int[2 + paramList.size() + paramList2.size()];
          int i = 0;
          clause[i++] = -getOperatorNr(oNr);
          clause[i++] = -getOperatorNr(oNr2);
          for (Pair<Integer, Integer> paramPos : paramList) {
            Argument a = predicate.getArguments().get(paramPos.getLeft());
            clause[i++] = -getParameterId(oNr, paramPos.getRight(), constantId.get(a));
          }
          for (Pair<Integer, Integer> paramPos : paramList2) {
            Argument a = predicate.getArguments().get(paramPos.getLeft());
            clause[i++] = -getParameterId(oNr2, paramPos.getRight(), constantId.get(a));
          }
          universalClauses.add(clause);
        }
      }
      for (Pair<Integer, List<Pair<Integer, Integer>>> pair : effects.get(pNr * 2 + 1)) {
        int oNr = pair.getLeft();
        List<Pair<Integer, Integer>> paramList = pair.getRight();
        for (Pair<Integer, List<Pair<Integer, Integer>>> pair2 : preconditions.get(pNr * 2)) {
          int oNr2 = pair2.getLeft();
          if (oNr == oNr2) {
            continue;
          }
          List<Pair<Integer, Integer>> paramList2 = pair2.getRight();
          System.out.print("Operators " + oNr + " and " + oNr2 + " interfere on " + predicate);
          int[] clause = new int[2 + paramList.size() + paramList2.size()];
          int i = 0;
          clause[i++] = -getOperatorNr(oNr);
          clause[i++] = -getOperatorNr(oNr2);
          for (Pair<Integer, Integer> paramPos : paramList) {
            Argument a = predicate.getArguments().get(paramPos.getLeft());
            clause[i++] = -getParameterId(oNr, paramPos.getRight(), constantId.get(a));
          }
          for (Pair<Integer, Integer> paramPos : paramList2) {
            Argument a = predicate.getArguments().get(paramPos.getLeft());
            clause[i++] = -getParameterId(oNr2, paramPos.getRight(), constantId.get(a));
          }
          universalClauses.add(clause);
        }
      }
      {
        List<int[]> frameAxioms = new ArrayList<>();
        frameAxioms.add(new int[2]);
        // false -> true
        frameAxioms.get(0)[0] = getPredicateNr(pNr, false);
        frameAxioms.get(0)[1] = -getPredicateNr(pNr, true);
        for (Pair<Integer, List<Pair<Integer, Integer>>> pair : effects.get(pNr * 2)) {
          int oNr = pair.getLeft();
          List<Pair<Integer, Integer>> paramList = pair.getRight();
          // frame axioms
          List<int[]> newFrameAxioms = new ArrayList<>();
          for (int[] oldClause : frameAxioms) {
            {
              int[] clause = new int[oldClause.length + 1];
              System.arraycopy(oldClause, 0, clause, 0, oldClause.length);
              clause[clause.length - 1] = getOperatorNr(oNr);
              newFrameAxioms.add(clause);
            }
            for (Pair<Integer, Integer> paramPos : paramList) {
              Argument a = predicate.getArguments().get(paramPos.getLeft());
              int[] clause = new int[oldClause.length + 1];
              System.arraycopy(oldClause, 0, clause, 0, oldClause.length);
              clause[clause.length - 1] = getParameterId(oNr, paramPos.getRight(), constantId.get(a));
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
        // true -> false
        frameAxioms.get(0)[0] = -getPredicateNr(pNr, false);
        frameAxioms.get(0)[1] = getPredicateNr(pNr, true);
        for (Pair<Integer, List<Pair<Integer, Integer>>> pair : effects.get(pNr * 2 + 1)) {
          int oNr = pair.getLeft();
          List<Pair<Integer, Integer>> paramList = pair.getRight();
          // frame axioms
          List<int[]> newFrameAxioms = new ArrayList<>();
          for (int[] oldClause : frameAxioms) {
            {
              int[] clause = new int[oldClause.length + 1];
              System.arraycopy(oldClause, 0, clause, 0, oldClause.length);
              clause[clause.length - 1] = getOperatorNr(oNr);
              newFrameAxioms.add(clause);
            }
            for (Pair<Integer, Integer> paramPos : paramList) {
              Argument a = predicate.getArguments().get(paramPos.getLeft());
              int[] clause = new int[oldClause.length + 1];
              System.arraycopy(oldClause, 0, clause, 0, oldClause.length);
              clause[clause.length - 1] = getParameterId(oNr, paramPos.getRight(), constantId.get(a));
              newFrameAxioms.add(clause);
            }
          }
          frameAxioms = newFrameAxioms;
        }
        transitionClauses.addAll(frameAxioms);
      }
    }
  }

  protected List<Pair<Integer, Integer>> getParamList(int oNr, Condition c) {
    Operator o = operators.get(oNr);
    List<Pair<Integer, Integer>> paramList = new ArrayList<>();
    for (int i = 0; i < c.getArguments().size(); i++) {
      Argument a = c.getArguments().get(i);
      if (!a.isConstant()) {
        paramList.add(new Pair<>(i, o.getArguments().indexOf(a)));
      }
    }
    return paramList;
  }

  protected List<Condition> getFlatConditions(AbstractCondition ac) {
    List<Condition> result = new ArrayList<>();
    if (ac.getConditionType() == ConditionType.atomic) {
      result.add((Condition) ac);
    } else if (ac.getConditionType() == ConditionType.conjunction) {
      for (AbstractCondition elem : ((ConditionSet) ac).getConditions()) {
        if (elem.getConditionType() != ConditionType.atomic) {
          System.out.println("ERROR: condition not flat: " + ac);
          System.exit(1);
        }
        result.add((Condition) elem);
      }
    } else {
      System.out.println("ERROR: condition not flat: " + ac);
      System.exit(1);
    }
    return result;
  }

  protected int getPredicateNr(int pNr, boolean nextStep) {
    return pNr + (nextStep ? stepVars : 0) + 1;
  }

  protected List<Argument> getConstantsOfType(Type type) {
    if (!constantsOfType.containsKey(type)) {
      List<Argument> result = new ArrayList<>();
      for (int i = 0; i < constants.size(); i++) {
        if (problem.isTypeSupertypeOfType(constants.get(i).getType(), type)) {
          result.add(constants.get(i));
        }
      }
      constantsOfType.put(type, result);
    }
    return constantsOfType.get(type);
  }

  protected int getOperatorNr(int oNr) {
    return predicates.size() + oNr + 1;
  }

  protected int getParameterId(int oNr, int pos, int cNr) {
    int id = predicates.size() + operators.size() + 1;
    Operator o = operators.get(oNr);
    Argument a = constants.get(cNr);
    for (int i = 0; i < oNr; i++) {
      id += operatorParameters.get(i);
    }
    for (int i = 0; i < pos; i++) {
      id += getConstantsOfType(o.getArguments().get(i).getType()).size();
    }
    id += getConstantsOfType(o.getArguments().get(pos).getType()).indexOf(a);
    return id;
  }

  protected void setInitialState() {
    initialClauses = new ArrayList<>();
    Set<Integer> allInitial = new HashSet<Integer>();
    allInitial.addAll(problem.getInitialState().stream().map(c -> predicateId.get(c)).collect(Collectors.toSet()));
    for (int i = 0; i < predicates.size(); i++) {
      if (allInitial.contains(i)) {
        initialClauses.add(new int[] { getPredicateNr(i, false) });
      } else {
        initialClauses.add(new int[] { -getPredicateNr(i, false) });
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
    for (int i = 0; i < goal.length; i++) {
      if (goal[i] > 0) {
        goal[i] += stepVars;
      } else {
        goal[i] -= stepVars;
      }
    }
  }

  protected void setGoal() {
    if (problem.getGoals().size() != 1) {
      System.out.println("ERROR: more than one goal");
      System.exit(1);
    }
    System.out.println("goal");
    List<Condition> goalConditions = getFlatConditions(problem.getGoals().get(0));
    goal = new int[goalConditions.size()];
    for (int i = 0; i < goalConditions.size(); i++) {
      Condition c = goalConditions.get(i);
      goal[i] = (c.isNegated() ? -1 : 1) * getPredicateNr(predicateId.get(c), false);
    }
  }

  protected PlanningProblem problem;

  protected List<Type> types;
  protected Map<Type, Integer> typeId;
  protected List<Argument> constants;
  protected Map<Type, List<Argument>> constantsOfType;
  protected Map<Argument, Integer> constantId;
  protected List<Condition> predicates;
  protected Map<Condition, Integer> predicateId;
  protected List<Operator> operators;
  protected Map<Operator, Integer> operatorId;

  protected List<Integer> operatorParameters;
  protected List<List<Pair<Integer, List<Pair<Integer, Integer>>>>> preconditions;
  protected List<List<Pair<Integer, List<Pair<Integer, Integer>>>>> effects;
  protected List<int[]> initialClauses;
  protected List<int[]> universalClauses;
  protected int[] goal;
  protected List<int[]> transitionClauses;
  protected int stepVars;
  protected BiPredicate<Operator, Argument> isGrounded;
}
