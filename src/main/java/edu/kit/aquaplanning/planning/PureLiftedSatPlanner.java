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

import edu.kit.aquaplanning.Configuration;
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
import edu.kit.aquaplanning.util.Logger;
import edu.kit.aquaplanning.util.Pair;

public class PureLiftedSatPlanner extends LiftedPlanner {

  public PureLiftedSatPlanner(Configuration config) {
    super(config);
  }

  @Override
  public Plan findPlan(PlanningProblem p) {
    problem = p;
    Logger.log(Logger.INFO, "TIME0 Generate clauses");
    isGrounded = (o, a) -> a.getName().startsWith("?c") && false;
    grounder = new RelaxedPlanningGraphGrounder(config);
    // initialize the SAT solver
    // SatSolver solver = new SatSolver();
    Logger.log(Logger.INFO, "TIME1 Generating clauses");
    initIDs();
    generateClauses();
    Solution solution = incPlan();
    if (solution.steps == -1) {
      Logger.log(Logger.ERROR, "No solution found");
      System.exit(1);
    }
    Logger.log(Logger.INFO, "Makespan " + (solution.steps - 1));
    // int step = 0;

    // for (int[] clause : initialClauses) {
    // solver.addClause(clause);
    // }
    // Logger.log(Logger.INFO, "TIME2 Starting solver");
    // while (true) {
    // if (solver.isSatisfiable(goalClause)) {
    // Logger.log(Logger.INFO, "TIME3 Solution found in step " + step);
    // break;
    // }
    // Logger.log(Logger.INFO, "No solution found in step " + step);
    // for (int[] clause : universalClauses) {
    // solver.addClause(clause);
    // }
    // for (int[] clause : transitionClauses) {
    // solver.addClause(clause);
    // }
    // nextStep();
    // step++;
    // }

    grounder.ground(problem);
    // return extractPlan(solver.getModel(), step);
    // System.out.println("Satsolver: " + step);
    // System.out.println("Satsolver: " + solver.getModel().length);
    // for (int i: solver.getModel()) {
    // System.out.print(i + " ");
    // }
    // System.out.println("Incplan: " + solution.steps);
    // System.out.println("Incplan: " + solution.model.length);
    // for (int i: solution.model) {
    // System.out.print(i + " ");
    // }
    return extractPlan(solution.model, solution.steps);
    // return extractPlan(solver.getModel(), step);
  }

  protected Plan extractPlan(int[] model, int steps) {
    Plan plan = new Plan();
    for (int base = 0; base < steps * stepVars; base += stepVars) {
      for (Operator o : operators.keySet()) {
        int i = operators.get(o);
        if (model[getOperatorSatId(i) + base] > 0) {
          List<Argument> args = new ArrayList<>();
          for (int j = 0; j < o.getArguments().size(); j++) {
            if (o.getArguments().get(j).isConstant()) {
              args.add(null);
              continue;
            }
            boolean found = eligibleArguments.get(i).get(j).size() == 0;
            for (Argument arg : eligibleArguments.get(i).get(j).keySet()) {
              int k = eligibleArguments.get(i).get(j).get(arg);
              if (model[getParameterSatId(i, j, k) + base] >= 0) {
                args.add(arg);
                found = true;
                break;
              }
            }
            if (!found) {
              Logger.log(Logger.ERROR, "Parameter not set in solution");
              System.exit(1);
            }
          }
          Operator go = o.getOperatorWithGroundArguments(args);
          plan.appendAtBack(grounder.getAction(go));
        }
      }
    }
    return plan;
  }

  protected void initIDs() {
    satCounter = 1;
    constants = problem.getConstants();
    setPredicateIDs();
    setOperatorIDs();
    Logger.log(Logger.INFO, "Number of predicates: " + predicates.size());
    Logger.log(Logger.INFO, "Number of lifted operators: " + problem.getOperators().size());
    Logger.log(Logger.INFO, "Number of operators: " + operators.size());

    stepVars = satCounter - 1;
    Logger.log(Logger.INFO, "Number of SAT variables: " + stepVars);
  }

  protected void setPredicateIDs() {
    predicates = new HashMap<>();
    predicateSatId = new ArrayList<>();
    preconditionsPos = new ArrayList<>();
    preconditionsNeg = new ArrayList<>();
    effectsPos = new ArrayList<>();
    effectsNeg = new ArrayList<>();
    for (Predicate liftedPredicate : problem.getPredicates().values()) {
      Condition condition = new Condition(liftedPredicate);
      for (int i = 0; i < liftedPredicate.getNumArgs(); i++) {
        condition.addArgument(new Argument("?" + String.valueOf(i), liftedPredicate.getArgumentTypes().get(i)));
      }
      for (Condition predicate : groundCondition(condition)) {
        predicates.put(predicate, predicates.size());
        predicateSatId.add(satCounter++);
        preconditionsPos.add(new HashSet<>());
        preconditionsNeg.add(new HashSet<>());
        effectsPos.add(new HashSet<>());
        effectsNeg.add(new HashSet<>());
      }
    }
  }

  protected void setOperatorIDs() {
    operators = new HashMap<>();
    operatorSatId = new ArrayList<>();
    parameterSatId = new ArrayList<>();
    eligibleArguments = new ArrayList<>();
    for (Operator liftedOperator : problem.getOperators()) {
      int numParameters = liftedOperator.getArguments().size();
      // System.out.print("Grounded candidates: ");
      for (Operator newOperator : groundOperator(liftedOperator)) {
        // System.out.print(" " + o);
        int operatorId = operators.size();
        // System.out.println("New operator " + operatorId + ": " + newOperator);
        operators.put(newOperator, operatorId);
        operatorSatId.add(satCounter++);
        List<Map<Argument, Integer>> operatorArguments = new ArrayList<>();
        List<List<Integer>> satId = new ArrayList<>();
        for (int i = 0; i < numParameters; i++) {
          if (newOperator.getArguments().get(i).isConstant()) {
            satId.add(null);
            operatorArguments.add(null);
          } else {
            satId.add(new ArrayList<>());
            operatorArguments.add(new HashMap<>());
            for (Argument a : getConstantsOfType(newOperator.getArguments().get(i).getType())) {
              satId.get(i).add(satCounter++);
              operatorArguments.get(i).put(a, operatorArguments.get(i).size());
            }
          }
        }
        parameterSatId.add(satId);
        eligibleArguments.add(operatorArguments);
        for (boolean isPrecondition : Arrays.asList(true, false)) {
          Pair<ConditionSet, ConditionSet> split = isPrecondition
              ? grounder.splitCondition(newOperator.getPrecondition())
              : grounder.splitCondition(newOperator.getEffect());
          ConditionSet simpleSet = split.getLeft();
          for (AbstractCondition c : split.getRight().getConditions()) {
            if (c.getConditionType() != ConditionType.numericEffect) {
              Logger.log(Logger.ERROR, "Condition contains complex set: " + split);
              System.exit(1);
            }
          }
          for (AbstractCondition c : simpleSet.getConditions()) {
            if (c.getConditionType() != ConditionType.atomic) {
              Logger.log(Logger.ERROR, "A simple set of conditions contains non-atomic condition " + c + ".");
              System.exit(1);
              // continue;
            }
            Condition condition = (Condition) c;
            ParameterMatching matching = getParameterMatching(newOperator, condition);
            for (Condition groundCondition : groundOperatorCondition(newOperator, condition)) {
              List<Integer> position = new ArrayList<>();
              List<Integer> argumentId = new ArrayList<>();
              // System.out.println("for ground operator " + groundedOperator);
              // System.out.println("for operator " + newOperator);
              // System.out.println("Arguments: " + eligibleArguments.get(operatorId));
              // System.out.println("Predicate: " + condition);
              // System.out.println("GroundPredicate: " + groundCondition);
              for (int i = 0; i < matching.size(); i++) {
                position.add(matching.getOperatorPos(i));
                argumentId.add(matching.getArgumentId(groundCondition, i));
              }
              // System.out.println("Positions: " + position);
              // System.out.println("Ids: " + argumentId);
              if (groundCondition.isNegated()) {
                if (isPrecondition) {
                  preconditionsNeg.get(predicates.get(groundCondition.withoutNegation()))
                      .add(new Assignment(operatorId, position, argumentId));
                } else {
                  effectsNeg.get(predicates.get(groundCondition.withoutNegation()))
                      .add(new Assignment(operatorId, position, argumentId));
                }
              } else {
                if (isPrecondition) {
                  preconditionsPos.get(predicates.get(groundCondition))
                      .add(new Assignment(operatorId, position, argumentId));
                } else {
                  effectsPos.get(predicates.get(groundCondition)).add(new Assignment(operatorId, position, argumentId));
                }
              }
            }
          }
        }
      }
    }
  }

  protected void generateClauses() {
    universalClauses = new ArrayList<>();
    transitionClauses = new ArrayList<>();
    setInitialState();
    int numClauses;
    numClauses = addParameterClauses();
    Logger.log(Logger.INFO, "Parameterassignment: " + numClauses);
    numClauses = addConditionClauses();
    Logger.log(Logger.INFO, "Parameters imply conditions: " + numClauses);
    numClauses = addInterferenceClauses();
    Logger.log(Logger.INFO, "Interference: " + numClauses);
    numClauses = addFrameAxioms();
    Logger.log(Logger.INFO, "Frame axioms: " + numClauses);
    setGoal();
    Logger.log(Logger.INFO, "Number of clauses: " + (universalClauses.size() + transitionClauses.size()));
  }

  protected void setInitialState() {
    initialClauses = new ArrayList<>();
    for (Condition c : predicates.keySet()) {
      if (problem.getInitialState().contains(c)) {
        initialClauses.add(new int[] { getPredicateSatId(predicates.get(c), false) });
      } else {
        initialClauses.add(new int[] { -getPredicateSatId(predicates.get(c), false) });
      }
    }
    // System.out.println("Initial state: " + initialClauses);
  }

  protected int addParameterClauses() {
    int numClauses = 0;
    for (int oId : operators.values()) {
      for (int pos = 0; pos < eligibleArguments.get(oId).size(); pos++) {
        Map<Argument, Integer> arguments = eligibleArguments.get(oId).get(pos);
        if (arguments == null) {
          continue;
        }
        int numArgs = arguments.size();
        {
          // Operator -> each parameter
          int[] clause = new int[numArgs + 1];
          int counter = 0;
          clause[counter++] = -getOperatorSatId(oId);
          for (int aId : arguments.values()) {
            clause[counter++] = getParameterSatId(oId, pos, aId);
          }
          // System.out.print("Operator " + oId + " Param " + pos + ": [ ");
          // for (int i : clause) {
          // System.out.print(i + " ");
          // }
          // System.out.println("]");
          universalClauses.add(clause);
          numClauses++;
        }
        {
          // <=1 per Parameter
          for (int aId1 : arguments.values()) {
            for (int aId2 : arguments.values()) {
              if (aId1 >= aId2) {
                continue;
              }
              int[] clause = new int[2];
              clause[0] = -getParameterSatId(oId, pos, aId1);
              clause[1] = -getParameterSatId(oId, pos, aId2);
              universalClauses.add(clause);
              numClauses++;
            }
          }
        }
      }
    }
    return numClauses;
  }

  protected int addConditionClauses() {
    int numClauses = 0;
    for (int pId : predicates.values()) {
      for (boolean isPrecondition : Arrays.asList(true, false)) {
        for (boolean isPositive : Arrays.asList(true, false)) {
          // System.out.println("Condition: " + c);
          Set<Assignment> support;
          if (isPrecondition) {
            if (isPositive) {
              support = preconditionsPos.get(pId);
            } else {
              support = preconditionsNeg.get(pId);
            }
          } else {
            if (isPositive) {
              support = effectsPos.get(pId);
            } else {
              support = effectsNeg.get(pId);
            }
          }
          for (Assignment assignment : support) {
            int oId = assignment.getOperatorId();
            // System.out.println("Operator: " + oNr);
            int[] clause = new int[assignment.size() + 2];
            int counter = 0;
            clause[counter++] = -getOperatorSatId(oId);
            for (int i = 0; i < assignment.size(); i++) {
              clause[counter++] = -getParameterSatId(oId, assignment.getPosition(i), assignment.getArgumentId(i));
            }
            clause[counter++] = (isPositive ? 1 : -1) * getPredicateSatId(pId, !isPrecondition);
            // System.out.print("Operator " + oId + " supports " + pId + ": [ ");
            // for (int i : clause) {
            // System.out.print(i + " ");
            // }
            // System.out.println("]");
            if (isPrecondition) {
              universalClauses.add(clause);
            } else {
              transitionClauses.add(clause);
            }
            numClauses++;
          }
        }
      }
    }
    return numClauses;
  }

  protected int addInterferenceClauses() {
    int numClauses = 0;
    for (int pId : predicates.values()) {
      for (boolean isPositive : Arrays.asList(true, false)) {
        Set<Assignment> effectSupport;
        Set<Assignment> precondSupport;
        if (isPositive) {
          effectSupport = effectsPos.get(pId);
          precondSupport = preconditionsNeg.get(pId);
        } else {
          effectSupport = effectsNeg.get(pId);
          precondSupport = preconditionsPos.get(pId);
        }
        for (Assignment effectAssignment : effectSupport) {
          int effectOperatorId = effectAssignment.getOperatorId();
          for (Assignment precondAssignment : precondSupport) {
            int precondOperatorId = precondAssignment.getOperatorId();
            if (effectOperatorId == precondOperatorId) {
              continue;
            }
            int[] clause = new int[effectAssignment.size() + precondAssignment.size() + 2];
            int counter = 0;
            clause[counter++] = -getOperatorSatId(effectOperatorId);
            clause[counter++] = -getOperatorSatId(precondOperatorId);
            for (int i = 0; i < effectAssignment.size(); i++) {
              clause[counter++] = -getParameterSatId(effectOperatorId, effectAssignment.getPosition(i),
                  effectAssignment.getArgumentId(i));
            }
            for (int i = 0; i < precondAssignment.size(); i++) {
              clause[counter++] = -getParameterSatId(precondOperatorId, precondAssignment.getPosition(i),
                  precondAssignment.getArgumentId(i));
            }
            // System.out.print(
            // "Operator " + effectOperatorId + " interferes with " + precondOperatorId + "
            // on " + pId + ": [ ");
            // for (int i : clause) {
            // System.out.print(i + " ");
            // }
            // System.out.println("]");
            universalClauses.add(clause);
            numClauses++;
          }
        }
      }
    }
    return numClauses;
  }

  protected int addFrameAxioms() {
    int numClauses = 0;
    for (int pId : predicates.values()) {
      for (boolean isPositive : Arrays.asList(true, false)) {
        Set<Assignment> support;
        if (isPositive) {
          support = effectsPos.get(pId);
        } else {
          support = effectsNeg.get(pId);
        }
        List<int[]> dnf = new ArrayList<>();
        dnf.add(new int[] { (isPositive ? 1 : -1) * getPredicateSatId(pId, false) });
        dnf.add(new int[] { (isPositive ? -1 : 1) * getPredicateSatId(pId, true) });
        for (Assignment assignment : support) {
          int[] clause = new int[assignment.size() + 1];
          int counter = 0;
          clause[counter++] = getOperatorSatId(assignment.getOperatorId());
          for (int i = 0; i < assignment.size(); i++) {
            clause[counter++] = getParameterSatId(assignment.getOperatorId(), assignment.getPosition(i),
                assignment.getArgumentId(i));
          }
          // System.out
          // .print("Predicate " + pId + " has support from " + assignment.getOperatorId()
          // + ": [ ");
          // for (int i : clause) {
          // System.out.print(i + " ");
          // }
          // System.out.println("]");
          dnf.add(clause);
        }
        // System.out.println("DNF: " + dnf);
        // System.out.println("CNF: " + DNF2CNF(dnf));
        List<int[]> cnf = DNF2CNF(dnf);
        transitionClauses.addAll(cnf);
        numClauses += cnf.size();
      }
    }
    return numClauses;
  }

  protected void setGoal() {
    ConditionSet goalSet = new ConditionSet(ConditionType.conjunction);
    problem.getGoals().forEach(c -> goalSet.add(c));
    Pair<ConditionSet, ConditionSet> split = grounder.splitCondition(goalSet);
    ConditionSet simpleSet = split.getLeft();
    // if (split.getRight() != null) {
    // if (split.getRight().getConditions().size() > 0) {
    // Logger.log(Logger.ERROR, "Goal contains complex set: " + split);
    // System.exit(1);
    // }
    // }
    goalClause = new int[simpleSet.getConditions().size()];
    int counter = 0;
    for (AbstractCondition c : simpleSet.getConditions()) {
      Condition goal = (Condition) c;
      if (goal.isNegated()) {
        goalClause[counter++] = -getPredicateSatId(predicates.get(goal.withoutNegation()), false);
      } else {
        goalClause[counter++] = getPredicateSatId(predicates.get(goal), false);
      }
    }
    // System.out.println("Goal: " + goalClause);
  }

  protected Set<Condition> groundCondition(Condition condition) {
    Set<Condition> result = new HashSet<>();
    Stack<List<Argument>> work = new Stack<>();
    int numParameters = condition.getNumArgs();
    work.push(new ArrayList<>(condition.getArguments()));
    List<List<Argument>> groundArguments = new ArrayList<>();
    for (int i = 0; i < numParameters; i++) {
      if (!condition.getArguments().get(i).isConstant()) {
        groundArguments.add(getConstantsOfType(condition.getArguments().get(i).getType()));
      } else {
        groundArguments.add(null);
      }
    }
    while (!work.isEmpty()) {
      List<Argument> first = work.pop();
      int pos = -1;
      for (int i = 0; i < numParameters; i++) {
        if (!first.get(i).isConstant() && groundArguments.get(i) != null) {
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
        for (Argument a : groundArguments.get(pos)) {
          List<Argument> newList = new ArrayList<>(first);
          newList.set(pos, a);
          work.push(newList);
        }
      }
    }
    return result;
  }

  protected Set<Condition> groundOperatorCondition(Operator operator, Condition condition) {
    int oId = operators.get(operator);
    Set<Condition> result = new HashSet<>();
    Stack<List<Argument>> work = new Stack<>();
    int numParameters = condition.getNumArgs();
    work.push(new ArrayList<>(condition.getArguments()));
    ParameterMatching matching = getParameterMatching(operator, condition);
    List<List<Argument>> groundArguments = new ArrayList<>();
    while (!work.isEmpty()) {
      List<Argument> first = work.pop();
      int pos = -1;
      for (int i = 0; i < matching.size(); i++) {
        if (!first.get(matching.getPredicatePos(i)).isConstant()) {
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
        for (Argument a : eligibleArguments.get(oId).get(matching.getOperatorPos(pos)).keySet()) {
          List<Argument> newList = new ArrayList<>(first);
          newList.set(matching.getPredicatePos(pos), a);
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
    work.push(new ArrayList<>(operator.getArguments()));
    List<List<Argument>> groundArguments = new ArrayList<>();
    for (int i = 0; i < numParameters; i++) {
      if (!operator.getArguments().get(i).isConstant() && isGrounded.test(operator, operator.getArguments().get(i))) {
        groundArguments.add(getConstantsOfType(operator.getArguments().get(i).getType()));
      } else {
        groundArguments.add(null);
      }
    }
    while (!work.isEmpty()) {
      List<Argument> first = work.pop();
      int pos = -1;
      for (int i = 0; i < first.size(); i++) {
        if (!first.get(i).isConstant() && groundArguments.get(i) != null) {
          pos = i;
          break;
        }
      }
      if (pos == -1) {
        Operator o = operator.getOperatorWithGroundArguments(first);
        // o.removeConstantArguments();
        result.add(o);
      } else {
        for (Argument a : groundArguments.get(pos)) {
          List<Argument> newList = new ArrayList<>(first);
          newList.set(pos, a);
          work.push(newList);
        }
      }
    }
    return result;
  }

  protected List<Argument> getConstantsOfType(Type type) {
    List<Argument> result = new ArrayList<>();
    for (int i = 0; i < constants.size(); i++) {
      if (problem.isTypeSupertypeOfType(constants.get(i).getType(), type)) {
        result.add(constants.get(i));
      }
    }
    return result;
  }

  protected int getPredicateSatId(int pId, boolean nextStep) {
    return predicateSatId.get(pId) + (nextStep ? stepVars : 0);
  }

  protected int getOperatorSatId(int oId) {
    return operatorSatId.get(oId);
  }

  protected int getParameterSatId(int oId, int pos, int cId) {
    return parameterSatId.get(oId).get(pos).get(cId);
  }

  int satCounter;
  protected List<Argument> constants;
  protected List<Integer> predicateSatId;
  protected List<Integer> operatorSatId;
  protected List<List<List<Integer>>> parameterSatId;
  protected BiPredicate<Operator, Argument> isGrounded;
}
