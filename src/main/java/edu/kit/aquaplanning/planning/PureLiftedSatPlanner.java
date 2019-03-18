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
    isGrounded = (o, a) -> a.getName().startsWith("?g_");
    setIDs();
    generateClauses();
    // initialize the SAT solver
    SatSolver solver = new SatSolver();

    addInitialState(solver);
    goal = getGoal();
    satGoal = new int[goal.size()];
    for (int i = 0; i < goal.size(); i++) {
      satGoal[i] = goal.get(i);
    }
    satClauses = new ArrayList<>();
    for (List<Integer> clause : clauses) {
      int[] tmp = new int[clause.size()];
      for (int i = 0; i < clause.size(); i++) {
        tmp[i] = clause.get(i);
      }
      satClauses.add(tmp);
    }
    int step = 0;

    while (true) {
      if (solver.isSatisfiable(satGoal)) {
        System.out.println("Solution found in step " + step);
        break;
      }
      System.out.println("No solution found in step " + step);
      for (int[] clause : satClauses) {
        solver.addClause(clause);
      }
      nextStep();
      step++;
    }
    // Decode the plan
    Plan plan = new Plan();
    int[] model = solver.getModel();
    for (int s = 0; s < step; s++) {
      for (int i = 0; i < operators.size(); i++) {
        if (model[getOperatorId(i) + s * stepVars] > 0) {
          Operator o = operators.get(i);
          System.out.println("Original Operator: " + operators.get(i));
          System.out.print("Apply action " + i + " with");
          List<Argument> args = new ArrayList<>();
          for (int j = 0; j < o.getArguments().size(); j++) {
            Argument a = o.getArguments().get(j);
            boolean found = false;
            for (int k = 0; k < getConstants(a).size(); k++) {
              if (model[getParameterId(i, j, k) + s * stepVars] >= 0) {
                args.add(getConstants(a).get(k));
                System.out.print(" " + j + ": " + getConstants(a).get(k));
                found = true;
                break;
              }
            }
            if (!found) {
              System.out.println("ERROR: no parameter set in solution");
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
      int groundPos = -1;
      for (int i = 0; i < numParameters; i++) {
        if (!first.get(i).isConstant()) {
          groundPos = i;
          break;
        }
      }
      if (groundPos == -1) {
        Condition c = condition.copy();
        for (int i = 0; i < numParameters; i++) {
          c.getArguments().set(i, first.get(i));
        }
        result.add(c);
      } else {
        for (Argument a : getConstants(first.get(groundPos))) {
          List<Argument> newList = new ArrayList<>(first);
          newList.set(groundPos, a);
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
    List<Integer> groundPositions = new ArrayList<>();
    List<List<Argument>> groundArguments = new ArrayList<>();
    for (int i = 0; i < numParameters; i++) {
      if (isGrounded.test(operator, operator.getArguments().get(i))) {
        groundPositions.add(i);
        groundArguments.add(getConstants(operator.getArguments().get(i)));
      }
    }
    while (!work.isEmpty()) {
      List<Argument> first = work.pop();
      int groundPos = -1;
      for (int i = 0; i < groundPositions.size(); i++) {
        if (first.get(groundPositions.get(i)) == null) {
          groundPos = i;
          break;
        }
      }
      if (groundPos == -1) {
        Operator o = operator.getOperatorWithGroundArguments(first);
        o.removeConstantArguments();
        result.add(o);
      } else {
        for (Argument a : groundArguments.get(groundPos)) {
          List<Argument> newList = new ArrayList<>(first);
          newList.set(groundPositions.get(groundPos), a);
          work.push(newList);
        }
      }
    }
    return result;
  }

  protected void setIDs() {
    stepVars = 0;

    typeId = new HashMap<>();
    constants = new ArrayList<>();
    constantId = new HashMap<>();
    System.out.println("Types:");
    for (Argument a : problem.getConstants()) {
      if (!typeId.containsKey(a.getType())) {
        System.out.println(a.getType() + ": " + typeId.size());
        typeId.put(a.getType(), typeId.size());
        constants.add(new ArrayList<>());
      }
      int id = typeId.get(a.getType());
      getConstants(a).add(a);
      constantId.put(a, getConstants(a).size() - 1);
    }
    System.out.println("Constants:");
    System.out.println(constants);

    System.out.println("Predicates:");
    System.out.println(problem.getPredicates().values());
    predicates = new ArrayList<>();
    predicateId = new HashMap<>();
    preconditions = new ArrayList<>();
    effects = new ArrayList<>();
    for (Predicate p : problem.getPredicates().values()) {
      Condition condition = new Condition(p);
      for (Condition c : groundCondition(condition)) {
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
      }
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
        int numParameters = o.getArguments().stream().mapToInt(a -> getConstants(a).size()).sum();
        operatorParameters.add(numParameters);
        stepVars += numParameters;
        List<Condition> flatPreconditions = getFlatConditions(o.getPrecondition());
        {
          for (Condition c : flatPreconditions) {
            System.out.println("\tPrecondition " + c);
            List<Integer> paramList = getParamList(oNr, c);
            System.out.println("\t\tParameter mapping: " + paramList);
            for (Condition gc : groundCondition(c)) {
              if (predicateId.containsKey(gc)) {
                preconditions.get(predicateId.get(gc) * 2 + (gc.isNegated() ? 1 : 0)).add(new Pair<>(oNr, paramList));
              } else {
                System.out.println("ERROR: Precondition not in list");
              }
            }
          }
        }
        {
          List<Condition> flatEffects = getFlatConditions(o.getEffect());
          for (Condition c : flatEffects) {
            System.out.println("\tEffect " + c);
            List<Integer> paramList = getParamList(oNr, c);
            System.out.println("\t\tParameter mapping: " + paramList);
            for (Condition gc : groundCondition(c)) {
              if (predicateId.containsKey(gc)) {
                effects.get(predicateId.get(gc) * 2 + (gc.isNegated() ? 1 : 0)).add(new Pair<>(oNr, paramList));
              } else {
                System.out.println("ERROR: Effect not in list");
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
    clauses = new ArrayList<>();
    for (int oNr = 0; oNr < operators.size(); oNr++) {
      Operator operator = operators.get(oNr);
      System.out.println("Operator " + oNr);
      for (int pos = 0; pos < operator.getArguments().size(); pos++) {
        Argument argument = operator.getArguments().get(pos);
        List<Argument> argumentConstants = getConstants(argument);
        {
          // Operator -> each parameter
          System.out.print("\timplies " + argument + ": ");
          List<Integer> clause = new ArrayList<>();
          clause.add(-getOperatorId(oNr));
          for (int cNr = 0; cNr < argumentConstants.size(); cNr++) {
            clause.add(getParameterId(oNr, pos, cNr));
          }
          clauses.add(clause);
          System.out.println(clause);
        }
        {
          // <=1 per Parameter
          System.out.print("\tAM1 " + argument + ": ");
          for (int c1 = 0; c1 < argumentConstants.size(); c1++) {
            for (int c2 = c1 + 1; c2 < argumentConstants.size(); c2++) {
              List<Integer> clause = new ArrayList<>();
              clause.add(-getParameterId(oNr, pos, c1));
              clause.add(-getParameterId(oNr, pos, c2));
              clauses.add(clause);
              System.out.print(clause);
            }
          }
          System.out.println("");
        }
      }
    }
    for (int pNr = 0; pNr < predicates.size(); pNr++) {
      Condition predicate = predicates.get(pNr);
      // positive
      for (Pair<Integer, List<Pair<Integer, Integer>>> pair : groundPreconditions.get(pNr * 2)) {
        int oNr = pair.getLeft();
        List<Pair<Integer, Integer>> paramList = pair.getRight();
        {
          // action implies precondition
          System.out.print("Operator " + oNr + " has positive precondition " + predicate + ": ");
          List<Integer> clause = new ArrayList<>();
          clause.add(-getOperatorId(oNr));
          for (Pair<Integer, Integer> paramPos : paramList) {
            Argument a = predicate.getArguments().get(paramPos.getLeft());
            clause.add(-getParameterId(oNr, paramPos.getRight(), constantId.get(a)));
          }
          clause.add(getPredicateId(pNr, false));
          clauses.add(clause);
          System.out.println(clause);
        }
      }
      // negative
      for (Pair<Integer, List<Pair<Integer, Integer>>> pair : groundPreconditions.get(pNr * 2 + 1)) {
        int oNr = pair.getLeft();
        List<Pair<Integer, Integer>> paramList = pair.getRight();
        {
          // action implies precondition
          System.out.print("Operator " + oNr + " has negative precondition " + predicate + ": ");
          List<Integer> clause = new ArrayList<>();
          clause.add(-getOperatorId(oNr));
          for (Pair<Integer, Integer> paramPos : paramList) {
            Argument a = predicate.getArguments().get(paramPos.getLeft());
            clause.add(-getParameterId(oNr, paramPos.getRight(), constantId.get(a)));
          }
          clause.add(-getPredicateId(pNr, false));
          clauses.add(clause);
          System.out.println(clause);
        }
      }
      // positive
      for (Pair<Integer, List<Pair<Integer, Integer>>> pair : groundEffects.get(pNr * 2)) {
        int oNr = pair.getLeft();
        List<Pair<Integer, Integer>> paramList = pair.getRight();
        {
          // action implies effect
          System.out.print("Operator " + oNr + " has positive effect " + predicate + ": ");
          List<Integer> clause = new ArrayList<>();
          clause.add(-getOperatorId(oNr));
          for (Pair<Integer, Integer> paramPos : paramList) {
            Argument a = predicate.getArguments().get(paramPos.getLeft());
            clause.add(-getParameterId(oNr, paramPos.getRight(), constantId.get(a)));
          }
          clause.add(getPredicateId(pNr, true));
          clauses.add(clause);
          System.out.println(clause);
        }
      }
      // negative
      for (Pair<Integer, List<Pair<Integer, Integer>>> pair : groundEffects.get(pNr * 2 + 1)) {
        int oNr = pair.getLeft();
        List<Pair<Integer, Integer>> paramList = pair.getRight();
        {
          // action implies effect
          System.out.print("Operator " + oNr + " has negative effect " + predicate + ": ");
          List<Integer> clause = new ArrayList<>();
          clause.add(-getOperatorId(oNr));
          for (Pair<Integer, Integer> paramPos : paramList) {
            Argument a = predicate.getArguments().get(paramPos.getLeft());
            clause.add(-getParameterId(oNr, paramPos.getRight(), constantId.get(a)));
          }
          clause.add(-getPredicateId(pNr, true));
          clauses.add(clause);
          System.out.println(clause);
        }
      }
      // prevent interference
      for (Pair<Integer, List<Pair<Integer, Integer>>> pair : groundEffects.get(pNr * 2)) {
        int oNr = pair.getLeft();
        List<Pair<Integer, Integer>> paramList = pair.getRight();
        for (Pair<Integer, List<Pair<Integer, Integer>>> pair2 : groundPreconditions.get(pNr * 2 + 1)) {
          int oNr2 = pair2.getLeft();
          if (oNr == oNr2) {
            continue;
          }
          List<Pair<Integer, Integer>> paramList2 = pair2.getRight();
          if (paramList.size() != paramList2.size()) {
            System.out.println("ERROR: Argument length not equal");
          }
          System.out.print("Operators " + oNr + " and " + oNr2 + " interfere on " + predicate);
          List<Integer> clause = new ArrayList<>();
          clause.add(-getOperatorId(oNr));
          clause.add(-getOperatorId(oNr2));
          for (Pair<Integer, Integer> paramPos : paramList) {
            Argument a = predicate.getArguments().get(paramPos.getLeft());
            clause.add(-getParameterId(oNr, paramPos.getRight(), constantId.get(a)));
          }
          for (Pair<Integer, Integer> paramPos : paramList2) {
            Argument a = predicate.getArguments().get(paramPos.getLeft());
            clause.add(-getParameterId(oNr2, paramPos.getRight(), constantId.get(a)));
          }
          clauses.add(clause);
          System.out.println(clause);
        }
      }
      for (Pair<Integer, List<Pair<Integer, Integer>>> pair : groundEffects.get(pNr * 2 + 1)) {
        int oNr = pair.getLeft();
        List<Pair<Integer, Integer>> paramList = pair.getRight();
        for (Pair<Integer, List<Pair<Integer, Integer>>> pair2 : groundPreconditions.get(pNr * 2)) {
          int oNr2 = pair2.getLeft();
          if (oNr == oNr2) {
            continue;
          }
          List<Pair<Integer, Integer>> paramList2 = pair2.getRight();
          if (paramList.size() != paramList2.size()) {
            System.out.println("ERROR: Argument length not equal");
          }
          System.out.print("Operators " + oNr + " and " + oNr2 + " interfere on " + predicate);
          List<Integer> clause = new ArrayList<>();
          clause.add(-getOperatorId(oNr));
          clause.add(-getOperatorId(oNr2));
          for (Pair<Integer, Integer> paramPos : paramList) {
            Argument a = predicate.getArguments().get(paramPos.getLeft());
            clause.add(-getParameterId(oNr, paramPos.getRight(), constantId.get(a)));
          }
          for (Pair<Integer, Integer> paramPos : paramList2) {
            Argument a = predicate.getArguments().get(paramPos.getLeft());
            clause.add(-getParameterId(oNr2, paramPos.getRight(), constantId.get(a)));
          }
          clauses.add(clause);
          System.out.println(clause);
        }
      }
      {
        List<List<Integer>> frameAxioms = new ArrayList<>();
        frameAxioms.add(new ArrayList<>());
        // false -> true
        frameAxioms.get(0).add(getPredicateId(pNr, false));
        frameAxioms.get(0).add(-getPredicateId(pNr, true));
        for (Pair<Integer, List<Pair<Integer, Integer>>> pair : groundEffects.get(pNr * 2)) {
          int oNr = pair.getLeft();
          List<Pair<Integer, Integer>> paramList = pair.getRight();
          // frame axioms
          List<List<Integer>> newFrameAxioms = new ArrayList<>();
          for (int i = 0; i < frameAxioms.size(); i++) {
            {
              List<Integer> clause = new ArrayList<>(frameAxioms.get(i));
              clause.add(getOperatorId(oNr));
              newFrameAxioms.add(clause);
            }
            for (Pair<Integer, Integer> paramPos : paramList) {
              Argument a = predicate.getArguments().get(paramPos.getLeft());
              List<Integer> clause = new ArrayList<>(frameAxioms.get(i));
              clause.add(getParameterId(oNr, paramPos.getRight(), constantId.get(a)));
              newFrameAxioms.add(clause);
            }
          }
          frameAxioms = newFrameAxioms;
        }
        clauses.addAll(frameAxioms);
      }
      {
        List<List<Integer>> frameAxioms = new ArrayList<>();
        frameAxioms.add(new ArrayList<>());
        // false -> true
        frameAxioms.get(0).add(-getPredicateId(pNr, false));
        frameAxioms.get(0).add(getPredicateId(pNr, true));
        for (Pair<Integer, List<Pair<Integer, Integer>>> pair : groundEffects.get(pNr * 2 + 1)) {
          int oNr = pair.getLeft();
          List<Pair<Integer, Integer>> paramList = pair.getRight();
          // frame axioms
          List<List<Integer>> newFrameAxioms = new ArrayList<>();
          for (int i = 0; i < frameAxioms.size(); i++) {
            {
              List<Integer> clause = new ArrayList<>(frameAxioms.get(i));
              clause.add(getOperatorId(oNr));
              newFrameAxioms.add(clause);
            }
            for (Pair<Integer, Integer> paramPos : paramList) {
              Argument a = predicate.getArguments().get(paramPos.getLeft());
              List<Integer> clause = new ArrayList<>(frameAxioms.get(i));
              clause.add(getParameterId(oNr, paramPos.getRight(), constantId.get(a)));
              newFrameAxioms.add(clause);
            }
          }
          frameAxioms = newFrameAxioms;
        }
        clauses.addAll(frameAxioms);
      }
    }
    for (Pair<Integer, List<Pair<Integer, Integer>>> assignment : forbidden) {
      List<Integer> clause = new ArrayList<>();
      for (Pair<Integer, Integer> paramPos : assignment.getRight()) {
        clause.add(-getParameterId(assignment.getLeft(), paramPos.getLeft(), paramPos.getRight()));
      }
      clauses.add(clause);
    }
  }

  protected List<Integer> getParamList(int oNr, Condition c) {
    Operator o = operators.get(oNr);
    List<Integer> paramList = new ArrayList<>();
    for (int i = 0; i < c.getArguments().size(); i++) {
      Argument a = c.getArguments().get(i);
      paramList.add(a.isConstant() ? -1 : o.getArguments().indexOf(a));
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
          System.out.println("ERROR: condition not flat");
        }
        result.add((Condition) elem);
      }
    } else {
      System.out.println("ERROR: condition not flat");
    }
    return result;
  }

  protected int getPredicateId(int pNr, boolean nextStep) {
    return pNr + (nextStep ? stepVars : 0) + 1;
  }

  protected List<Argument> getConstants(Argument argument) {
    int id = typeId.getOrDefault(argument.getType(), -1);
    if (id > -1) {
      return constants.get(id);
    } else {
      return new ArrayList<Argument>();
    }
  }

  protected int getOperatorId(int oNr) {
    return predicates.size() + oNr + 1;
  }

  protected int getParameterId(int oNr, int pos, int cNr) {
    int id = predicates.size() + operators.size() + 1;
    Operator o = operators.get(oNr);
    for (int i = 0; i < oNr; i++) {
      id += operatorParameters.get(i);
    }
    for (int i = 0; i < pos; i++) {
      id += getConstants(o.getArguments().get(i)).size();
    }
    id += cNr;
    return id;
  }

  protected void addInitialState(SatSolver solver) {
    Set<Integer> allInitial = new HashSet<Integer>();
    allInitial.addAll(problem.getInitialState().stream().map(c -> predicateId.get(c)).collect(Collectors.toSet()));
    for (int i = 0; i < predicates.size(); i++) {
      if (allInitial.contains(i)) {
        solver.addClause(new int[] { getPredicateId(i, false) });
      } else {
        solver.addClause(new int[] { -getPredicateId(i, false) });
      }
    }
  }

  protected void nextStep() {
    for (int[] clause : satClauses) {
      for (int i = 0; i < clause.length; i++) {
        if (clause[i] > 0) {
          clause[i] += stepVars;
        } else {
          clause[i] -= stepVars;
        }
      }
    }
    for (int i = 0; i < satGoal.length; i++) {
      if (satGoal[i] > 0) {
        satGoal[i] += stepVars;
      } else {
        satGoal[i] -= stepVars;
      }
    }
  }

  protected List<Integer> getGoal() {
    if (problem.getGoals().size() != 1) {
      System.out.println("ERROR: more than one goal");
    }
    List<Condition> goalConditions = getFlatConditions(problem.getGoals().get(0));
    List<Integer> goalClauses = new ArrayList<>();
    for (Condition g : goalConditions) {
      goalClauses.add(getPredicateId(predicateId.get(g), false));
    }
    return goalClauses;
  }

  protected PlanningProblem problem;

  protected Map<Type, Integer> typeId;
  protected List<List<Argument>> constants;
  protected Map<Argument, Integer> constantId;
  protected List<Condition> predicates;
  protected Map<Condition, Integer> predicateId;
  protected List<Operator> operators;
  protected Map<Operator, Integer> operatorId;

  protected List<Integer> operatorParameters;
  protected List<List<Pair<Integer, List<Integer>>>> preconditions;
  protected List<List<Pair<Integer, List<Integer>>>> effects;
  protected List<int[]> initialClauses;
  protected List<int[]> universalClauses;
  protected List<int[]> goalClauses;
  protected List<int[]> transitionalClauses;
  protected int stepVars;
  protected BiPredicate<Operator, Argument> isGrounded;
}
