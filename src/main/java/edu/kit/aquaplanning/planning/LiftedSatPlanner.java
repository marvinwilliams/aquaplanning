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
  public Plan findPlan(PlanningProblem problem) {
    RelaxedPlanningGraphGrounder grounder = new RelaxedPlanningGraphGrounder(config);
    RelaxedPlanningGraph graph = grounder.initGrounding(problem, (o, a) -> a.getName().startsWith("?x"));
    System.out.println(graph.getLiftedState(graph.getCurrentLayer()));
    List<Condition> predicates = new ArrayList<>();
    for (Condition c : graph.getLiftedState(graph.getCurrentLayer())) {
      predicates.addAll(groundPredicate(problem, c));
    }
    List<Operator> operators = graph.getLiftedActions();
    for (Operator o : operators) {
      o.removeConstantArguments();
    }

    setIDs(graph.getLiftedState(graph.getCurrentLayer()),
    // graph.getLiftedActions());
    // initialize the SAT solver
    SatSolver solver = new SatSolver();

    addInitialState(problem, predicates, solver);
    int step = 0;
    int count;

    while (true) {
      for (Operator o : operators) {
        int oId = getOperatorId(o, step);
        count = 0;
        for (Type t : o.getArgumentTypes()) {
          int numConstantsOfType = constantsPerType.get(t).size();
          // Operator -> each parameter
          int[] parameters = new int[numConstantsOfType + 1];
          parameters[0] = -oId;
          for (int i = 1; i < numConstantsOfType + 1; i++) {
            parameters[i] = getParameterId(o, count, step) + i - 1;
          }
          solver.addClause(parameters);
          // AtMostOne Const per Parameter
          for (int i = 0; i < numConstantsOfType; i++) {
            for (int j = i + 1; j < numConstantsOfType; j++) {
              solver.addClause(new int[] { getParameterId(o, count, step) + i, getParameterId(o, count, step) + j });
            }
          }
          count++;
        }
        // Operator implies Precond and Effects
        List<Condition> preconditions = new ArrayList<>();
        if (o.getPrecondition().getConditionType() == ConditionType.atomic) {
          preconditions.add((Condition) o.getPrecondition());
        } else if (o.getPrecondition().getConditionType() == ConditionType.conjunction) {
          for (AbstractCondition ac : ((ConditionSet) o.getPrecondition()).getConditions()) {
            preconditions.add((Condition) ac);
          }
        } else {
          System.out.println("ERROR: not a flat precondition");
        }
        for (Condition liftedPrecondition : preconditions) {
          List<Pair<Integer, Integer>> parameterPos = new ArrayList<>();
          count = 0;
          for (Argument a : ((Condition) liftedPrecondition).getArguments()) {
            if (!a.isConstant()) {
              parameterPos.add(new Pair<>(count, o.getArguments().indexOf(a)));
            }
            count++;
          }
          Set<Condition> groundPreconditions = groundPredicate(problem, liftedPrecondition);
          for (Condition c : groundPreconditions) {
            int pId = predicateId.getOrDefault(c, -1);
            // Ground precond not relevant
            if (pId == -1) {
              int[] clause = new int[parameterPos.size()];
              count = 0;
              for (Pair<Integer, Integer> p : parameterPos) {
                clause[count++] = -(getParameterId(o, p.getRight(), step) + constantsPerType
                    .get(o.getArgumentTypes().get(p.getRight())).indexOf(c.getArguments().get(p.getLeft())));
              }
              solver.addClause(clause);
            } else {
              int[] clause = new int[parameterPos.size() + 2];
              clause[0] = getOperatorId(o, step);
              count = 1;
              for (Pair<Integer, Integer> p : parameterPos) {
                clause[count++] = -(getParameterId(o, p.getRight(), step) + constantsPerType
                    .get(o.getArgumentTypes().get(p.getRight())).indexOf(c.getArguments().get(p.getLeft())));
              }
              clause[count] = (c.isNegated() ? -1:1) * getPredicateId(c, step);
              solver.addClause(clause);
            }
          }
        }

        // Forbid parallelism

        // Assume goal

        // Frame axioms
      }

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

  protected Set<Condition> groundPredicate(PlanningProblem problem, Condition predicate) {
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

  protected void setIDs(PlanningProblem problem, List<Condition> predicates, List<Operator> operators) {
    stepVars = predicates.size() + operators.size();
    constantsPerType = new HashMap<>();
    negEffects = new ArrayList<>();
    posEffects = new ArrayList<>();
    for (Argument a : problem.getConstants()) {
      constantsPerType.putIfAbsent(a.getType(), new ArrayList<Argument>());
      constantsPerType.get(a.getType()).add(a);
    }
    int count = 0;
    predicateId = new HashMap<>();
    for (Condition c : predicates) {
      predicateId.put(c, count++);
      negEffects.add(new ArrayList<>());
      posEffects.add(new ArrayList<>());
    }
    count = 0;
    operatorId = new HashMap<>();
    numParameters = new ArrayList<>();
    for (Operator o : operators) {
      operatorId.put(o, count++);
      numParameters
          .add(o.getArgumentTypes().stream().map(t -> constantsPerType.get(t).size()).reduce(0, (x, y) -> x + y));
      stepVars += numParameters.get(count);
      List<Condition> effects = new ArrayList<>();
      if (o.getEffect().getConditionType() == ConditionType.atomic) {
        effects.add((Condition) o.getEffect());
      } else if (o.getEffect().getConditionType() == ConditionType.conjunction) {
        for (AbstractCondition ac: ((ConditionSet) o.getEffect()).getConditions()) {
          effects.add((Condition) ac);
        }
      } else {
        System.out.println("ERROR: effects not flat");
      }
      for (Condition c: effects) {
          List<Pair<Integer, Integer>> parameterPos = new ArrayList<>();
          count = 0;
          for (Argument a : ((Condition) liftedPrecondition).getArguments()) {
            if (!a.isConstant()) {
              parameterPos.add(new Pair<>(count, o.getArguments().indexOf(a)));
            }
            count++;
          }
      }
    }
  }

  protected int getPredicateId(Condition cond, int step) {
    int id = predicateId.get(cond);
    return stepVars * step + id + 1;
  }

  protected int getOperatorId(Operator operator, int step) {
    int id = operatorId.get(operator);
    return stepVars * step + predicateId.size() + id + 1;
  }

  protected int getParameterId(Operator operator, int pos, int step) {
    int id = 0;
    for (int i = 0; i < operatorId.get(operator); i++) {
      id += numParameters.get(i);
    }
    for (int i = 0; i < pos; i++) {
      id += constantsPerType.get(operator.getArgumentTypes().get(i)).size();
    }
    return stepVars * step + predicateId.size() + operatorId.size() + id + 1;
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

  protected Map<Type, List<Argument>> constantsPerType;
  protected List<Integer> numParameters;
  protected List<List<Pair<Integer, List<Pair<Integer, Argument>>>>> negEffects;
  protected List<List<Pair<Integer, List<Pair<Integer, Argument>>>>> posEffects;
  protected int stepVars;
}
