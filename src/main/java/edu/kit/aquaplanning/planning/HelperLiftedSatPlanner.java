package edu.kit.aquaplanning.planning;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Collectors;

import edu.kit.aquaplanning.Configuration;
import edu.kit.aquaplanning.grounding.RelaxedPlanningGraph;
import edu.kit.aquaplanning.grounding.RelaxedPlanningGraphGrounder;
import edu.kit.aquaplanning.model.ground.GroundPlanningProblem;
import edu.kit.aquaplanning.model.ground.Plan;
import edu.kit.aquaplanning.model.lifted.Argument;
import edu.kit.aquaplanning.model.lifted.Operator;
import edu.kit.aquaplanning.model.lifted.PlanningProblem;
import edu.kit.aquaplanning.model.lifted.Type;
import edu.kit.aquaplanning.model.lifted.condition.AbstractCondition;
import edu.kit.aquaplanning.model.lifted.condition.AbstractCondition.ConditionType;
import edu.kit.aquaplanning.model.lifted.condition.Condition;
import edu.kit.aquaplanning.model.lifted.condition.ConditionSet;
import edu.kit.aquaplanning.sat.SatSolver;
import edu.kit.aquaplanning.util.Pair;

public class LiftedSatPlanner extends LiftedPlanner {

  public LiftedSatPlanner(Configuration config) {
    super(config);
  }

  @Override
  public Plan findPlan(PlanningProblem p) {
    problem = p;
    RelaxedPlanningGraphGrounder grounder = new RelaxedPlanningGraphGrounder(config);
    GroundPlanningProblem graph = grounder.ground(problem);
    grounder.ground(problem);
    stepVars = 0;
    predicates = new ArrayList<>();
    predicateId = new HashMap<>();
    groundPreconditions = new ArrayList<>();
    groundEffects = new ArrayList<>();
    System.out.println("Constants:");
    System.out.println(problem.getConstants());
    System.out.println("Lifted predicates:");
    System.out.println(graph.getLiftedState(graph.getCurrentLayer()));
    for (Condition c : graph.getLiftedState(graph.getCurrentLayer())) {
      if (c.isNegated()) {
        System.out.println("ERROR: predicate in plangraph negated");
        c = c.withoutNegation();
      }
      for (Condition gc : groundPredicate(c)) {
        if (predicateId.containsKey(gc)) {
          continue;
        }
        predicates.add(gc);
        predicateId.put(gc, predicates.size() - 1);
        gc = gc.withoutNegation();
        gc.setNegated(true);
        predicateId.put(gc, predicates.size() - 1);
        groundPreconditions.add(new ArrayList<>());
        groundPreconditions.add(new ArrayList<>());
        groundEffects.add(new ArrayList<>());
        groundEffects.add(new ArrayList<>());
        stepVars++;
      }
    }
    System.out.println("Grounded predicates:");
    System.out.println(predicates);
    operators = graph.getLiftedActions();
    stepVars += operators.size();
    for (Operator o : operators) {
      o.removeConstantArguments();
    }
    System.out.println("Operators:");
    System.out.println(operators);
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

  protected Set<Condition> groundPredicate(Condition predicate) {
    Set<Condition> result = new HashSet<>();
    Stack<Condition> work = new Stack<Condition>();
    work.add(predicate);
    while (!work.isEmpty()) {
      Condition first = work.pop();
      int groundPos = -1;
      for (int i = 0; i < first.getNumArgs(); i++) {
        if (!first.getArguments().get(i).isConstant()) {
          groundPos = i;
          break;
        }
      }
      if (groundPos == -1) {
        result.add(first);
        continue;
      }
      for (Argument a : problem.getConstants()) {
        if (problem.isArgumentOfType(a, first.getArguments().get(groundPos).getType())) {
          Condition copy = first.copy();
          copy.getArguments().set(groundPos, a);
          work.push(copy);
        }
      }
    }
    return result;
  }

  protected void setIDs() {
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
      constants.get(id).add(a);
      constantId.put(a, constants.get(id).size() - 1);
    }
    operatorParameters = new ArrayList<>();
    forbidden = new ArrayList<>();
    for (int oNr = 0; oNr < operators.size(); oNr++) {
      System.out.println("Operator " + oNr);
      Operator operator = operators.get(oNr);
      System.out.println(operator);
      int numParameters = operator.getArguments().stream().mapToInt(a -> getConstants(a).size()).sum();
      operatorParameters.add(numParameters);
      System.out.println("\t #Parameters: " + numParameters);
      stepVars += numParameters;
      {
        List<Condition> preconditions = getFlatConditions(operator.getPrecondition());
        for (Condition c : preconditions) {
          System.out.println("\tPrecondition " + c);
          List<Pair<Integer, Integer>> paramList = getParamList(oNr, c);
          System.out.println("\t\tParameter mapping: " + paramList);
          for (Condition gc : groundPredicate(c)) {
            if (predicateId.containsKey(gc)) {
              groundPreconditions.get(predicateId.get(gc) * 2 + (gc.isNegated() ? 1 : 0))
                  .add(new Pair<>(oNr, paramList));
            } else {
              List<Pair<Integer, Integer>> forbiddenAssignment = new ArrayList<>();
              for (Pair<Integer, Integer> paramPos : paramList) {
                forbiddenAssignment
                    .add(new Pair<>(paramPos.getRight(), constantId.get(gc.getArguments().get(paramPos.getLeft()))));
              }
              forbidden.add(new Pair<>(oNr, forbiddenAssignment));
            }
          }
        }
      }
      {
        List<Condition> effects = getFlatConditions(operator.getEffect());
        for (Condition c : effects) {
          System.out.println("\tEffect " + c);
          List<Pair<Integer, Integer>> paramList = getParamList(oNr, c);
          System.out.println("\t\tParameter mapping: " + paramList);
          for (Condition gc : groundPredicate(c)) {
            if (predicateId.containsKey(gc)) {
              groundEffects.get(predicateId.get(gc) * 2 + (gc.isNegated() ? 1 : 0)).add(new Pair<>(oNr, paramList));
            } else {
              List<Pair<Integer, Integer>> forbiddenAssignment = new ArrayList<>();
              for (Pair<Integer, Integer> paramPos : paramList) {
                forbiddenAssignment
                    .add(new Pair<>(paramPos.getRight(), constantId.get(gc.getArguments().get(paramPos.getLeft()))));
              }
              forbidden.add(new Pair<>(oNr, forbiddenAssignment));
            }
          }
        }
      }
    }
    System.out.println("GroundPreconditions: " + groundPreconditions);
    System.out.println("GroundEffects: " + groundEffects);
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
    if (argument.isConstant()) {
      System.out.println("ERROR: argument is const");
    }
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

  protected List<Condition> predicates;
  protected Map<Condition, Integer> predicateId;
  protected List<Operator> operators;
  protected Map<Operator, Integer> operatorId;
  protected Map<Type, Integer> typeId;
  protected List<List<Argument>> constants;
  protected Map<Argument, Integer> constantId;

  protected List<Integer> operatorParameters;
  protected List<List<Pair<Integer, List<Pair<Integer, Integer>>>>> groundPreconditions;
  protected List<List<Pair<Integer, List<Pair<Integer, Integer>>>>> groundEffects;
  protected List<Pair<Integer, List<Pair<Integer, Integer>>>> forbidden;
  protected List<List<Integer>> clauses;
  protected List<int[]> satClauses;
  protected List<Integer> goal;
  protected int[] satGoal;
  protected int stepVars;
}
