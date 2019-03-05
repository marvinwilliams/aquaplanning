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
      allInitial.add(getPredicateId(c.getPredicate().getName(), c.getArguments(), 0));
      System.out.println(c.getPredicate());
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
      Predicate predicate = predicates.get(n);
      predicateId.put(n, count);
      System.out.println("Predicate " + n + " has base " + count);
      int argcount = 1;
      for (Type t : predicate.getArgumentTypes()) {
        argcount *= constantsPerType.get(t);
      }
      count += argcount;
    }
    stepVars = count;

    List<Operator> operators = problem.getOperators();
    operatorId = new HashMap<String, Integer>();
    count = 0;
    for (Operator o : operators) {
      operatorId.put(o.getName(), count);
      int opcount = 1;
      int argcount = 1;
      for (Argument a : o.getArguments()) {
        if (getsGrounded(o, a)) {
          opcount *= constantsPerType.get(a.getType());
        } else {
          argcount *= constantsPerType.get(a.getType());
        }
      }
      stepVars += argcount;
      count += opcount;
    }
    stepVars += count;
  }

  protected boolean getsGrounded(Operator op, Argument arg) {
    return arg.getName().startsWith("g_");
  }

  protected int getPredicateId(String name, List<Argument> arguments, int step) {
    int id = predicateId.get(name);
    int factor = 1;
    for (int i = 1; i < arguments.size(); i++) {
      factor *= constantsPerType.get(arguments.get(i).getType());
    }
    Argument a_next = arguments.get(0);
    for (int i = 0; i < arguments.size(); i++) {
      Argument a = a_next;
      id += constantId.get(a.getName()) * factor;
      if (i < arguments.size() - 1) {
        a_next = arguments.get(i + 1);
        factor /= constantsPerType.get(a_next.getType());
      }
    }
    return step * stepVars + id + 1;
  }

  protected int getOperatorId(String name, List<Argument> groundedArgs, int step) {
    int id = predicateId.size() + operatorId.get(name);
    int factor = 1;
    for (int i = 1; i < groundedArgs.size(); i++) {
      factor *= constantsPerType.get(groundedArgs.get(i).getType());
    }
    Argument a_next = groundedArgs.get(0);
    for (int i = 0; i < groundedArgs.size(); i++) {
      Argument a = a_next;
      id += constantId.get(a.getName()) * factor;
      if (i < groundedArgs.size() - 1) {
        a_next = groundedArgs.get(i + 1);
        factor /= constantsPerType.get(a_next.getType());
      }
    }
    return step * stepVars + id + 1;
  }

  protected Map<String, Integer> predicateId;
  protected Map<String, Integer> constantId;
  protected Map<String, Integer> operatorId;
  protected Map<Type, Integer> constantsPerType;
  protected int stepVars;
}
