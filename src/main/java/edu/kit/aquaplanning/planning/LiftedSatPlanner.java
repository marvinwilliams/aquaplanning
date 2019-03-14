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
    RelaxedPlanningGraph graph = grounder.initGrounding(problem, (o, a) -> a.getName().startsWith("?x"));
    stepVars = 0;
    predicates = new ArrayList<>();
    predicateId = new HashMap<>();
    groundPreconditions = new ArrayList<>();
    groundEffects = new ArrayList<>();
    for (Condition c : graph.getLiftedState(graph.getCurrentLayer())) {
      System.out.println("Lifted: " + c);
      if (c.isNegated()) {
        System.out.println("ERROR: predicate in plangraph negated");
        c = c.withoutNegation();
      }
      for (Condition gc : groundPredicate(c)) {
        System.out.println("Added " + gc);
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
    operators = graph.getLiftedActions();
    stepVars += operators.size();
    for (Operator o : operators) {
      o.removeConstantArguments();
    }
    setIDs();
    generateClauses();
    // initialize the SAT solver
    SatSolver solver = new SatSolver();

    addInitialState(solver);
    int step = 0;

    while (true) {
      List<Integer> goal = getGoal();
      int[] assumptions = new int[goal.size()];
      for (int i = 0; i < goal.size(); i++) {
        assumptions[i] = goal.get(i);
      }
      if (solver.isSatisfiable(assumptions)) {
        System.out.println("Solution found!");
        break;
      }
      System.out.println("No solution found in step " + step);
      for (List<Integer> clause : clauses) {
        int[] tmp = new int[clause.size()];
        for (int i = 0; i < clause.size(); i++) {
          tmp[i] = clause.get(i);
        }
        solver.addClause(tmp);
      }
      nextStep();
      step++;
    }
    // find the plan
    // int step = 0;
    // while (true) {

    // if (solver.isSatisfiable(assumptions)) {
    // break;
    // }
    // if (!withinComputationalBounds(step + 1)) {
    // // No plan found in the given computational bounds
    // return null;
    // }
    // step++;
    // }

    // Decode the plan
    Plan plan = new Plan();
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
    for (Argument a : problem.getConstants()) {
      if (!typeId.containsKey(a.getType())) {
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
      Operator operator = operators.get(oNr);
      int numParameters = operator.getArgumentTypes().stream().mapToInt(t -> constants.get(typeId.get(t)).size()).sum();
      operatorParameters.add(numParameters);
      stepVars += numParameters;
      {
        List<Condition> preconditions = getFlatConditions(operator.getPrecondition());
        for (Condition c : preconditions) {
          List<Pair<Integer, Integer>> paramList = getParamList(oNr, c);
          for (Condition gc : groundPredicate(c)) {
            System.out.println(gc + " " + predicateId.get(gc));
            if (predicateId.containsKey(gc)) {
              groundPreconditions.get(predicateId.get(gc) + (gc.isNegated() ? 1 : 0)).add(new Pair<>(oNr, paramList));
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
          List<Pair<Integer, Integer>> paramList = getParamList(oNr, c);
          for (Condition gc : groundPredicate(c)) {
            if (predicateId.containsKey(gc)) {
              groundEffects.get(predicateId.get(gc) + (gc.isNegated() ? 1 : 0)).add(new Pair<>(oNr, paramList));
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
  }

  protected void generateClauses() {
    clauses = new ArrayList<>();
    for (int oNr = 0; oNr < operators.size(); oNr++) {
      Operator operator = operators.get(oNr);
      for (int pos = 0; pos < operator.getArguments().size(); pos++) {
        Argument argument = operator.getArguments().get(pos);
        List<Argument> argumentConstants = constants.get(typeId.get(argument.getType()));
        {
          // Operator -> each parameter
          List<Integer> clause = new ArrayList<>();
          clause.add(-getOperatorId(oNr));
          for (int cNr = 0; cNr < argumentConstants.size(); cNr++) {
            clause.add(getParameterId(oNr, pos, cNr));
          }
          clauses.add(clause);
        }
        {
          // <=1 per Parameter
          for (int c1 = 0; c1 < argumentConstants.size(); c1++) {
            for (int c2 = c1 + 1; c2 < argumentConstants.size(); c2++) {
              List<Integer> clause = new ArrayList<>();
              clause.add(-getParameterId(oNr, pos, c1));
              clause.add(-getParameterId(oNr, pos, c2));
              clauses.add(clause);
            }
          }
        }
      }
    }
    for (int pNr = 0; pNr < predicates.size(); pNr++) {
      Condition predicate = predicates.get(pNr);
      // positive
      for (Pair<Integer, List<Pair<Integer, Integer>>> pair : groundPreconditions.get(pNr)) {
        int oNr = pair.getLeft();
        List<Pair<Integer, Integer>> paramList = pair.getRight();
        {
          // action implies precondition
          List<Integer> clause = new ArrayList<>();
          clause.add(-getOperatorId(oNr));
          for (Pair<Integer, Integer> paramPos : paramList) {
            Argument a = predicate.getArguments().get(paramPos.getLeft());
            clause.add(-getParameterId(oNr, paramPos.getRight(), constantId.get(a)));
          }
          clause.add(getPredicateId(pNr, false));
          clauses.add(clause);
        }
      }
      // negative
      for (Pair<Integer, List<Pair<Integer, Integer>>> pair : groundPreconditions.get(pNr + 1)) {
        int oNr = pair.getLeft();
        List<Pair<Integer, Integer>> paramList = pair.getRight();
        {
          // action implies precondition
          List<Integer> clause = new ArrayList<>();
          clause.add(-getOperatorId(oNr));
          for (Pair<Integer, Integer> paramPos : paramList) {
            Argument a = predicate.getArguments().get(paramPos.getLeft());
            clause.add(-getParameterId(oNr, paramPos.getRight(), constantId.get(a)));
          }
          clause.add(-getPredicateId(pNr, false));
          clauses.add(clause);
        }
      }
      // positive
      for (Pair<Integer, List<Pair<Integer, Integer>>> pair : groundEffects.get(pNr)) {
        int oNr = pair.getLeft();
        List<Pair<Integer, Integer>> paramList = pair.getRight();
        {
          // action implies effect
          List<Integer> clause = new ArrayList<>();
          clause.add(-getOperatorId(oNr));
          for (Pair<Integer, Integer> paramPos : paramList) {
            Argument a = predicate.getArguments().get(paramPos.getLeft());
            clause.add(-getParameterId(oNr, paramPos.getRight(), constantId.get(a)));
          }
          clause.add(getPredicateId(pNr, true));
          clauses.add(clause);
        }
      }
      // negative
      for (Pair<Integer, List<Pair<Integer, Integer>>> pair : groundEffects.get(pNr + 1)) {
        int oNr = pair.getLeft();
        List<Pair<Integer, Integer>> paramList = pair.getRight();
        {
          // action implies effect
          List<Integer> clause = new ArrayList<>();
          clause.add(-getOperatorId(oNr));
          for (Pair<Integer, Integer> paramPos : paramList) {
            Argument a = predicate.getArguments().get(paramPos.getLeft());
            clause.add(-getParameterId(oNr, paramPos.getRight(), constantId.get(a)));
          }
          clause.add(-getPredicateId(pNr, true));
          clauses.add(clause);
        }
      }
      // prevent interference
      for (Pair<Integer, List<Pair<Integer, Integer>>> pair : groundEffects.get(pNr)) {
        int oNr = pair.getLeft();
        List<Pair<Integer, Integer>> paramList = pair.getRight();
        for (Pair<Integer, List<Pair<Integer, Integer>>> pair2 : groundPreconditions.get(pNr + 1)) {
          int oNr2 = pair2.getLeft();
          if (oNr == oNr2) {
            continue;
          }
          List<Pair<Integer, Integer>> paramList2 = pair2.getRight();
          if (paramList.size() != paramList2.size()) {
            System.out.println("ERROR: Argument length not equal");
          }
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
        }
      }
      for (Pair<Integer, List<Pair<Integer, Integer>>> pair : groundEffects.get(pNr + 1)) {
        int oNr = pair.getLeft();
        List<Pair<Integer, Integer>> paramList = pair.getRight();
        for (Pair<Integer, List<Pair<Integer, Integer>>> pair2 : groundPreconditions.get(pNr)) {
          int oNr2 = pair2.getLeft();
          if (oNr == oNr2) {
            continue;
          }
          List<Pair<Integer, Integer>> paramList2 = pair2.getRight();
          if (paramList.size() != paramList2.size()) {
            System.out.println("ERROR: Argument length not equal");
          }
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
        }
      }
      {
        List<List<Integer>> frameAxioms = new ArrayList<>();
        frameAxioms.add(new ArrayList<>());
        // false -> true
        frameAxioms.get(0).add(getPredicateId(pNr, false));
        frameAxioms.get(0).add(-getPredicateId(pNr, true));
        for (Pair<Integer, List<Pair<Integer, Integer>>> pair : groundEffects.get(pNr)) {
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
        for (Pair<Integer, List<Pair<Integer, Integer>>> pair : groundEffects.get(pNr + 1)) {
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
        result.add((Condition) elem);
      }
    } else {
      System.out.println("ERROR: effects not flat");
    }
    return result;
  }

  protected int getPredicateId(int pNr, boolean nextStep) {
    // even numbers are not negated, odd numbers are negated
    return pNr + (nextStep ? stepVars : 0) + 1;
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
      id += constants.get(typeId.get(o.getArgumentTypes().get(i))).size();
    }
    id += cNr;
    return id;
  }

  protected void addInitialState(SatSolver solver) {
    Set<Integer> allInitial = new HashSet<Integer>();
    allInitial.addAll(problem.getInitialState().stream().map(c -> predicateId.get(c)).collect(Collectors.toSet()));
    for (int i = 0; i < predicates.size(); i += 2) {
      if (allInitial.contains(i)) {
        solver.addClause(new int[] { getPredicateId(i, false) });
      } else {
        solver.addClause(new int[] { getPredicateId(i + 1, false) });
      }
    }
  }

  protected void nextStep() {
    for (List<Integer> clause : clauses) {
      for (int i = 0; i < clause.size(); i++) {
        clause.set(i, clause.get(i) + stepVars);
      }
    }
  }

  protected List<Integer> getGoal() {
    if (problem.getGoals().size() != 1) {
      System.out.println("ERROR: more than one goal");
    }
    List<Condition> goal = getFlatConditions(problem.getGoals().get(0));
    List<Integer> goalClauses = new ArrayList<>();
    for (Condition g : goal) {
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
  protected int stepVars;
}
