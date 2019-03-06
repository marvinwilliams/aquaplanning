package edu.kit.aquaplanning.planning;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import edu.kit.aquaplanning.Configuration;
import edu.kit.aquaplanning.model.ground.Plan;
import edu.kit.aquaplanning.model.lifted.Argument;
import edu.kit.aquaplanning.model.lifted.Operator;
import edu.kit.aquaplanning.model.lifted.PlanningProblem;
import edu.kit.aquaplanning.model.lifted.Predicate;
import edu.kit.aquaplanning.model.lifted.Type;
import edu.kit.aquaplanning.model.lifted.condition.Condition;
import edu.kit.aquaplanning.sat.SatSolver;

public class LiftedSatPlanner extends LiftedPlanner {

  public LiftedSatPlanner(Configuration config) {
    super(config);
  }

  @Override
  public Plan findPlan(PlanningProblem problem) {
    setIDs(problem);
    // initialize the SAT solver
    SatSolver solver = new SatSolver();
    addInitialState(problem, solver);
    for (Operator o: problem.getOperators()) {
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

  protected void addInitialState(PlanningProblem problem, SatSolver solver) {
    Set<Integer> allInitial = new HashSet<Integer>();
    System.out.println("Initial state");
    for (Condition c : problem.getInitialState()) {
      int pId = getPredicateId(c.getPredicate().getName(), c.getArguments(), 0);
      allInitial.add(pId);
      System.out.println(c + " -> " + pId);
    }
    for (int i = 1; i < stepVars + 1; i++) {
      if (allInitial.contains(i)) {
        System.out.println("Added clause " + i);
        solver.addClause(new int[] { i });
      } else {
        solver.addClause(new int[] { -i });
      }
    }
  }

  protected void setIDs(PlanningProblem problem) {
    int numConstants = problem.getConstants().size();
    constantsPerType = new HashMap<Type, Integer>();

    List<Argument> constants = problem.getConstants();
    constantId = new HashMap<String, Integer>();
    int count = 0;
    for (Argument a : constants) {
      constantsPerType.putIfAbsent(a.getType(), 0);
      constantsPerType.put(a.getType(), constantsPerType.get(a.getType()) + 1);
      constantId.put(a.getName(), count);
      count++;
    }

    Map<String, Predicate> predicates = problem.getPredicates();
    predicateId = new HashMap<String, Integer>();
    count = 0;
    for (String n : predicates.keySet()) {
      Predicate pred = predicates.get(n);
      predicateId.put(n, count);
      System.out.println("Predicate " + n + " has base " + count);
      if (pred.getNumArgs() == 0) {
        count += 1;
      } else {
        count += getNumFactorized(pred.getArgumentTypes());
      }
    }
    stepVars = count;

    List<Operator> operators = problem.getOperators();
    operatorId = new HashMap<String, Integer>();
    count = 0;
    for (Operator o : operators) {
      operatorId.put(o.getName(), count);
      System.out.println("Operator " + o.getName() + " has base " + count);
      List<Type> groundedTypes = o.getArguments().stream().filter(a -> isGrounded(o, a)).map(a -> a.getType())
          .collect(Collectors.toList());
      List<Argument> liftedArguments = o.getArguments().stream().filter(a -> !isGrounded(o, a))
          .collect(Collectors.toList());
      System.out.println("Operator " + o.getName() + " has " + o.getArguments().size() + " arguments, "
          + groundedTypes.size() + " are grounded and " + liftedArguments.size() + " are lifted");
      for (Argument a : liftedArguments) {
        stepVars += constantsPerType.get(a.getType());
      }
      if (groundedTypes.isEmpty()) {
        count += 1;
      } else {
        count += getNumFactorized(groundedTypes);
      }
    }
    stepVars += count;
  }

  protected int getNumFactorized(List<Type> types) {
    if (types.isEmpty()) {
      return 0;
    }
    int factor = 1;
    for (Type t : types) {
      factor *= constantsPerType.get(t);
    }
    return factor;
  }

  protected int getPosition(List<Argument> args) {
    if (args.isEmpty()) {
      return 0;
    }
    List<Type> types = new ArrayList<Type>();
    for (Argument a : args) {
      types.add(a.getType());
    }
    int factor = getNumFactorized(types);
    int pos = 0;
    for (Argument a : args) {
      factor /= constantsPerType.get(a.getType());
      pos += constantId.get(a.getName()) * factor;
    }
    return pos;
  }

  protected boolean isGrounded(Operator op, Argument arg) {
    return arg.getName().startsWith("?p");
  }

  protected int getPredicateId(String name, List<Argument> args, int step) {
    int id = predicateId.get(name);
    id += getPosition(args);
    return stepVars * step + id + 1;
  }

  protected int getOperatorId(String name, List<Argument> groundedArgs, int step) {
    int id = predicateId.size();
    id += operatorId.get(name) + getPosition(groundedArgs);
    return stepVars * step + id + 1;
  }

  protected Map<String, Integer> predicateId;
  protected Map<String, Integer> constantId;
  protected Map<String, Integer> operatorId;
  protected Map<Type, Integer> constantsPerType;
  protected int stepVars;
}
