package edu.kit.aquaplanning.planning;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.kit.aquaplanning.Configuration;
import edu.kit.aquaplanning.model.ground.Plan;
import edu.kit.aquaplanning.model.lifted.Argument;
import edu.kit.aquaplanning.model.lifted.Operator;
import edu.kit.aquaplanning.model.lifted.PlanningProblem;
import edu.kit.aquaplanning.model.lifted.Predicate;
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

    // find the plan
    // int step = 0;
    // while (true) {

    //   if (solver.isSatisfiable(assumptions)) {
    //     break;
    //   }
    //   if (!withinComputationalBounds(step + 1)) {
    //     // No plan found in the given computational bounds
    //     return null;
    //   }
    //   step++;
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
      allInitial.add(getPredicateId(c.getPredicate().getName(), c.getArguments(), 0));
      System.out.println(c.getPredicate());
    }
    for (int i = 1; i < stepVars + 1; i++) {
      if (allInitial.contains(i)) {
        System.out.println("Added clause " + i);
        solver.addClause(new int[] {i});
      } else {
        solver.addClause(new int[] {-i});
      }
    }
  }

  protected void setIDs(PlanningProblem problem) {
    int count = 1;
    stepVars = 0;
    int numConstants = problem.getConstants().size();
    System.out.println("There are " + numConstants + " constants");
    System.out.println("There are " + problem.getOperators().size() + " operators");
    Map<String, Predicate> predicates = problem.getPredicates();
    System.out.println("Predicates..");
    predicateBaseId = new HashMap<String, Integer>();
    for (String n : predicates.keySet()) {
      Predicate predicate = predicates.get(n);
      predicateBaseId.put(n, count);
      System.out.println("Predicate " + n + " has " + predicate.getNumArgs() + " args and base " + count);
      count += Math.pow(numConstants, predicate.getNumArgs());
    }
    stepVars += count - 1;
    count = 1;
    List<Argument> constants = problem.getConstants();
    constantId = new HashMap<String, Integer>();
    for (Argument a : constants) {
      constantId.put(a.getName(), count);
      count++;
    }
    stepVars += count - 1;
    count = 1;
    List<Operator> operators = problem.getOperators();
    operatorId = new HashMap<String, Integer>();
    for (Operator o : operators) {
      operatorId.put(o.getName(), count);
      count++;
    }
    stepVars += count - 1;
  }

  protected int getPredicateId(String name, List<Argument> arguments, int step) {
    int id = predicateBaseId.get(name);
    int factor = (int) Math.pow(constantId.size(), arguments.size() - 1);
    for (Argument a : arguments) {
      id += constantId.get(a.getName()) * factor;
      factor /= constantId.size();
    }
    return id * (step + 1);
  }

  protected int getConstantId(String name, int step) {
    return constantId.get(name) * (step + 1);
  }

  protected int getOperatorId(String name, int step) {
    return operatorId.get(name) * (step + 1);
  }

  protected Map<String, Integer> predicateBaseId;
  protected Map<String, Integer> constantId;
  protected Map<String, Integer> operatorId;
  protected int stepVars;
}
