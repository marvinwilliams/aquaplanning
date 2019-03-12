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
    int count;
    typeId = new HashMap<>();
    count = 0;
    for (Argument a : problem.getConstants()) {
      if (!typeId.containsKey(a.getType())) {
        typeId.put(a.getType(), count);
        constantsPerType.add(new ArrayList<>());
        count++;
      }
      constantsPerType.get(typeId.get(a.getType())).add(a);
    }
    posEffects = new ArrayList<>();
    negEffects = new ArrayList<>();
    for (int i = 0; i < predicates.size(); i++) {
      posEffects.add(new ArrayList<>());
      negEffects.add(new ArrayList<>());
    }
    numParameters = new ArrayList<>();
    for (Operator o : operators) {
      numParameters.add(o.getArgumentTypes().stream().map(t -> constantsPerType.get(typeId.get(t)).size()).reduce(0,
          (x, y) -> x + y));
      List<Condition> effects = getFlatConditions(o.getEffect());
      for (Condition c : effects) {
        List<Integer> paramList = new ArrayList<>();
        paramList.add(operators.indexOf(o));
        paramList.addAll(getParamList(o, c));
        for (Condition gc : groundPredicate(c)) {
          if (gc.isNegated()) {
            negEffects.get(predicates.indexOf(gc)).add(paramList);
          } else {
            posEffects.get(predicates.indexOf(gc)).add(paramList);
          }
        }
      }
    }
  }

  protected void generateClauses() {
    clauses = new ArrayList<>();
    for (int oNr = 0; oNr < operators.size(); oNr++) {
      Operator operator = operators.get(oNr);
      for (int i = 0; i < operator.getArguments().size(); i++) {
        Argument argument = operator.getArguments().get(i);
        List<Argument> constants = constantsPerType.get(typeId.get(argument.getType()));
        {
          // Operator -> each parameter
          List<Integer> clause = new ArrayList<>();
          clause.add(-getOperatorId(operator));
          for (Argument c : constants) {
            clause.add(getParameterId(operator, i, c));
          }
          clauses.add(clause);
        }
        {
          // AtMostOne Const per Parameter
          for (Argument c1 : constants) {
            for (Argument c2 : constants) {
              int id1 = getParameterId(operator, i, c1);
              int id2 = getParameterId(operator, i, c2);
              if (id1 < id2) {
                List<Integer> clause = new ArrayList<>();
                clause.add(-id1);
                clause.add(-id2);
                clauses.add(clause);
              }
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
            clause.add(-getOperatorId(operator));
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
            clause.add(-getOperatorId(operator));
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
    {
      // Frame axioms
    }
  }

  protected List<Integer> getParamList(Operator operator, Condition c) {
    List<Integer> paramList = new ArrayList<>();
    for (Argument a : c.getArguments()) {
      if (a.isConstant()) {
        paramList.add(-1);
      } else {
        paramList.add(operator.getArguments().indexOf(a));
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

  protected int getPredicateId(Condition cond) {
    return predicates.indexOf(cond) + 1;
  }

  protected int getOperatorId(Operator operator) {
    return predicates.size() + operators.indexOf(operator) + 1;
  }

  protected int getParameterId(Operator operator, int pos, Argument constant) {
    int id = predicates.size() + operators.size() + 1;
    for (int i = 0; i < operators.indexOf(operator); i++) {
      id += numParameters.get(i);
    }
    for (int i = 0; i < pos; i++) {
      id += constantsPerType.get(typeId.get(operator.getArgumentTypes().get(i))).size();
    }
    id += constantsPerType.get(typeId.get(constant.getType())).indexOf(constant);
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
  protected List<Condition> predicates;
  protected List<Operator> operators;
  protected Map<Type, Integer> typeId;
  protected List<List<Argument>> constantsPerType;
  protected List<Integer> numParameters;
  protected List<List<List<Integer>>> negEffects;
  protected List<List<List<Integer>>> posEffects;
  protected List<List<Integer>> clauses;
  protected int stepVars;
}
