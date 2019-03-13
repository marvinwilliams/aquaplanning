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
    predicates = new ArrayList<>();
    for (Condition c : graph.getLiftedState(graph.getCurrentLayer())) {
      predicates.addAll(groundPredicate(c));
    }
    operators = graph.getLiftedActions();
    for (Operator o : operators) {
      o.removeConstantArguments();
    }
    setIDs();
    generateClauses();
    // initialize the SAT solver
    SatSolver solver = new SatSolver();

    addInitialState(problem, predicates, solver);
    int step = 0;
    int count;

    while (true) {

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
    int[] model = solver.getModel();
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
    types = new ArrayList<>();
    for (Argument a : problem.getConstants()) {
      if (!types.contains(a.getType())) {
        types.add(a.getType());
        constantsPerType.add(new ArrayList<>());
      }
      constantsPerType.get(types.indexOf(a.getType())).add(a);
    }
    groundPreconditions = new ArrayList<>();
    groundEffects = new ArrayList<>();
    for (int i = 0; i < predicates.size(); i++) {
      groundPreconditions.add(new ArrayList<>());
      groundPreconditions.add(new ArrayList<>());
      groundEffects.add(new ArrayList<>());
      groundEffects.add(new ArrayList<>());
      if (predicates.get(i).isNegated()) {
        System.out.println("ERROR: Not negated predicate in plan graph");
      }
    }
    numParameters = new ArrayList<>();
    for (int i = 0; i < operators.size(); i++) {
      Operator operator = operators.get(i);
      numParameters
          .add(operator.getArgumentTypes().stream().mapToInt(t -> constantsPerType.get(types.indexOf(t)).size()).sum());
      {
        List<Condition> effects = getFlatConditions(operator.getEffect());
        for (Condition c : effects) {
          List<Integer> paramList = getParamList(i, c);
          Set<Condition> groundConditions = groundPredicate(c);
          if (c.isNegated()) {
            for (Condition gc : groundPredicate(c)) {
              groundEffects.get(predicates.indexOf(gc.withoutNegation())).get(1).add(new Pair<>(i, paramList));
            }
          } else {
            for (Condition gc : groundPredicate(c)) {
              groundEffects.get(predicates.indexOf(gc)).get(0).add(new Pair<>(i, paramList));
            }
          }
        }
      }
      {
        List<Condition> preconditions = getFlatConditions(operator.getPrecondition());
        for (Condition c : preconditions) {
          List<Integer> paramList = getParamList(i, c);
          Set<Condition> groundConditions = groundPredicate(c);
          if (c.isNegated()) {
            for (Condition gc : groundPredicate(c)) {
              groundPreconditions.get(predicates.indexOf(gc.withoutNegation())).get(1).add(new Pair<>(i, paramList));
            }
          } else {
            for (Condition gc : groundPredicate(c)) {
              groundPreconditions.get(predicates.indexOf(gc)).get(0).add(new Pair<>(i, paramList));
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
        List<Argument> constants = constantsPerType.get(types.indexOf(argument.getType()));
        {
          // Operator -> each parameter
          List<Integer> clause = new ArrayList<>();
          clause.add(-getOperatorId(oNr));
          for (int cNr = 0; cNr < constants.size(); cNr++) {
            clause.add(getParameterId(oNr, pos, cNr));
          }
          clauses.add(clause);
        }
        {
          // <=1 per Parameter
          for (int c1 = 0; c1 < constants.size(); c1++) {
            for (int c2 = c1 + 1; c2 < constants.size(); c2++) {
              List<Integer> clause = new ArrayList<>();
              clause.add(-getParameterId(oNr, pos, c1));
              clause.add(-getParameterId(oNr, pos, c2));
              clauses.add(clause);
            }
          }
        }
      }
      {
        // Operator implies Preconditions
        List<Condition> preconditions = getFlatConditions(operator.getPrecondition());
        for (Condition c : preconditions) {
          List<Integer> paramList = getParamList(operator, c);
          for (Condition gc : groundPredicate(c)) {
            List<Integer> clause = new ArrayList<>();
            clause.add(-getOperatorId(oNr));
            for (int i = 0; i < paramList.size(); i++) {
              if (paramList.get(i) > -1) {
                clause.add(-getParameterId(operator, paramList.get(i), gc.getArguments().get(i)));
              }
            }
            if (predicates.contains(gc)) {
              clause.add((gc.isNegated() ? -1 : 1) * getPredicateId(gc));
              clauses.add(clause);
            } else {
              if (gc.isNegated()) {
                // not in predicates and negative -> rigid, trivially true
              } else {
                // not in predicates but required -> not reachable
                clauses.add(clause);
              }
            }
          }
        }
      }
      {
        // Operator implies Effects
        List<Condition> effects = getFlatConditions(operator.getEffect());
        for (Condition c : effects) {
          List<Integer> paramList = getParamList(operator, c);
          for (Condition gc : groundPredicate(c)) {
            List<Integer> clause = new ArrayList<>();
            clause.add(-getOperatorId(oNr));
            for (int i = 0; i < paramList.size(); i++) {
              if (paramList.get(i) > -1) {
                clause.add(-getParameterId(operator, paramList.get(i), gc.getArguments().get(i)));
              }
            }
            if (predicates.contains(gc)) {
              clause.add((gc.isNegated() ? -1 : 1) * (getPredicateId(gc) + stepVars));
              clauses.add(clause);
            } else {
              if (gc.isNegated()) {
                // not in predicates and negative -> rigid, trivially true
              } else {
                // not in predicates but required -> not reachable
                clauses.add(clause);
              }
            }
          }
        }
      }
      {
        // Forbid interference
        for (Operator other : operators) {
          if (other == operator) {
            continue;
          }
          for (Condition effect : getFlatConditions(operator.getEffect())) {
            List<Integer> paramList1 = getParamList(operator, effect);
            for (Condition precondition : getFlatConditions(other.getPrecondition())) {
              if (effect.getPredicate().equals(precondition.getPredicate())) {
                if (effect.isNegated() != precondition.isNegated()) {
                  List<Integer> paramList2 = getParamList(other, precondition);
                  Set<Condition> groundedPreconditions = groundPredicate(precondition.withoutNegation());
                  for (Condition groundedEffect : groundPredicate(effect.withoutNegation())) {
                    if (groundedPreconditions.contains(groundedEffect)) {
                      List<Integer> clause = new ArrayList<>();
                      clause.add(-getOperatorId(operator));
                      clause.add(-getOperatorId(other));
                      for (int i = 0; i < groundedEffect.getNumArgs(); i++) {
                        if (paramList1.get(i) > -1) {
                          clause
                              .add(-getParameterId(operator, paramList1.get(i), groundedEffect.getArguments().get(i)));
                        }
                        if (paramList2.get(i) > -1) {
                          clause.add(-getParameterId(other, paramList2.get(i), groundedEffect.getArguments().get(i)));
                        }
                      }
                      clauses.add(clause);
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    for (int pNr = 0; pNr < predicates.size(); pNr++) {
      Condition predicate = predicates.get(pNr);

      for (int ispos = 0; ispos < 2; ispos++) {
        for (Pair<Integer, List<Integer>> pair : groundEffects.get(pNr).get(ispos)) {
          int o = pair.getLeft();
          List<Integer> paramList = pair.getRight();
          {
            // prevent interference
            for (Pair<Integer, List<Integer>> pair2 : groundPreconditions.get(pNr).get(1 - ispos)) {
              int o2 = pair2.getLeft();
              if (o == o2) {
                continue;
              }
              List<Integer> paramList2 = pair2.getRight();
              if (paramList.size() != paramList2.size()) {
                System.out.println("ERROR: Argument length not equal");
              }
              List<Integer> clause = new ArrayList<>();
              clause.add(-getOperatorId(o));
              clause.add(-getOperatorId(o2));
              for (int pos = 0; pos < paramList.size(); pos++) {
                Argument argument = predicate.getArguments().get(pos);
                if (paramList.get(pos) > -1) {
                  clause.add(-getParameterId(o, paramList.get(pos),
                      constantsPerType.get(types.indexOf(argument.getType())).indexOf(argument)));
                }
                if (paramList2.get(pos) > -1) {
                  clause.add(-getParameterId(o2, paramList2.get(pos),
                      constantsPerType.get(types.indexOf(argument.getType())).indexOf(argument)));
                }
              }
              clauses.add(clause);
            }
          }
          {
            // frame axioms
          }
        }
      }
    }
  }

  protected List<Integer> getParamList(int oNr, Condition c) {
    Operator o = operators.get(oNr);
    List<Integer> paramList = new ArrayList<>();
    for (Argument a : c.getArguments()) {
      if (a.isConstant()) {
        paramList.add(-1);
      } else {
        paramList.add(o.getArguments().indexOf(a));
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

  protected int getPredicateId(int pNr) {
    return pNr + 1;
  }

  protected int getOperatorId(int oNr) {
    return predicates.size() + oNr + 1;
  }

  protected int getParameterId(int oNr, int pos, int cNr) {
    int id = predicates.size() + operators.size() + 1;
    Operator o = operators.get(oNr);
    for (int i = 0; i < oNr; i++) {
      id += numParameters.get(i);
    }
    for (int i = 0; i < pos; i++) {
      id += constantsPerType.get(types.indexOf(o.getArgumentTypes().get(i))).size();
    }
    id += cNr;
    return id;
  }

  protected void addInitialState(PlanningProblem problem, Set<Condition> predicates, SatSolver solver) {
    Set<Integer> allInitial = new HashSet<Integer>();
    System.out.println("Initial state");
    allInitial.addAll(problem.getInitialState().stream().map(c -> getPredicateId(c, 0)).collect(Collectors.toSet()));
    for (int i = 1; i < predicateId.size() + 1; i++) {
      if (allInitial.contains(i)) {
        solver.addClause(new int[] { i });
      } else {
        solver.addClause(new int[] { -i });
      }
    }
  }

  protected PlanningProblem problem;

  protected List<Argument> constants;
  protected List<Condition> predicates;
  protected List<Operator> operators;
  protected List<Type> types;
  protected List<List<Argument>> constantsPerType;

  protected List<Integer> numParameters;
  protected List<List<List<Pair<Integer, List<Integer>>>>> groundPreconditions;
  protected List<List<List<Pair<Integer, List<Integer>>>>> groundEffects;
  protected List<List<Integer>> clauses;
  protected int stepVars;
}
