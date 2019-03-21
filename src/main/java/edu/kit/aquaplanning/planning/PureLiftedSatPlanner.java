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
import edu.kit.aquaplanning.sat.SatSolver;
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
    setIDs();
    generateClauses();
    Logger.log(Logger.INFO, "TIME1");
    // initialize the SAT solver
    SatSolver solver = new SatSolver();

    int step = 0;

    for (int[] clause : initialClauses) {
      solver.addClause(clause);
    }
    Logger.log(Logger.INFO, "TIME2 Starting solver");
    while (true) {
      if (solver.isSatisfiable(goal)) {
        Logger.log(Logger.INFO, "TIME3 Solution found in step " + step);
        break;
      }
      Logger.log(Logger.INFO, "No solution found in step " + step);
      for (int[] clause : universalClauses) {
        solver.addClause(clause);
      }
      for (int[] clause : transitionClauses) {
        solver.addClause(clause);
      }
      nextStep();
      step++;
    }
    // Decode the plan
    Plan plan = new Plan();
    RelaxedPlanningGraphGrounder grounder = new RelaxedPlanningGraphGrounder(config);
    grounder.ground(problem);
    int[] model = solver.getModel();
    for (int s = 0; s < step; s++) {
      for (int i = 0; i < operators.size(); i++) {
        if (model[getOperatorNr(i) + s * stepVars] > 0) {
          Operator o = operators.get(i);
          List<Argument> args = new ArrayList<>();
          for (int j = 0; j < o.getArguments().size(); j++) {
            if (o.getArguments().get(j).isConstant()) {
              args.add(null);
              continue;
            }
            boolean found = eligibleConstants.get(i).get(j).size() == 0;
            for (int k = 0; k < eligibleConstants.get(i).get(j).size(); k++) {
              if (model[getParameterId(i, j, k) + s * stepVars] >= 0) {
                args.add(constants.get(eligibleConstants.get(i).get(j).get(k)));
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

  protected void setIDs() {
    int satCounter = 1;

    constants = new ArrayList<>();
    constantId = new HashMap<>();
    for (Argument a : problem.getConstants()) {
      constantId.put(a, constants.size());
      constants.add(a);
    }
    Logger.log(Logger.INFO, "Number of constants: " + constants.size());

    predicates = new ArrayList<>();
    predicateSatId = new ArrayList<>();
    predicateId = new HashMap<>();
    conditionLookup = new ArrayList<>();
    Logger.log(Logger.INFO, "Number of lifted predicates: " + problem.getPredicates().size());
    for (Predicate liftedPredicate : problem.getPredicates().values()) {
      Condition condition = new Condition(liftedPredicate);
      for (int i = 0; i < liftedPredicate.getNumArgs(); i++) {
        condition.addArgument(new Argument("?" + String.valueOf(i), liftedPredicate.getArgumentTypes().get(i)));
      }
      for (Condition p : groundCondition(condition)) {
        predicateId.put(p, predicates.size());
        Condition neg = p.withoutNegation();
        neg.setNegated(true);
        predicateId.put(neg, predicates.size());
        predicates.add(p);
        conditionLookup.add(new ArrayList<>());
        conditionLookup.get(conditionLookup.size() - 1).add(new ArrayList<>());
        conditionLookup.get(conditionLookup.size() - 1).add(new ArrayList<>());
        conditionLookup.get(conditionLookup.size() - 1).get(0).add(new ArrayList<>());
        conditionLookup.get(conditionLookup.size() - 1).get(0).add(new ArrayList<>());
        conditionLookup.get(conditionLookup.size() - 1).get(1).add(new ArrayList<>());
        conditionLookup.get(conditionLookup.size() - 1).get(1).add(new ArrayList<>());
        predicateSatId.add(satCounter++);
      }
    }
    Logger.log(Logger.INFO, "Number of predicates: " + predicates.size());

    operators = new ArrayList<>();
    operatorSatId = new ArrayList<>();
    operatorId = new HashMap<>();
    parameterSatId = new ArrayList<>();
    eligibleConstants = new ArrayList<>();
    Logger.log(Logger.INFO, "Number of lifted operators: " + problem.getOperators().size());
    for (Operator liftedOperator : problem.getOperators()) {
      int numParameters = liftedOperator.getArguments().size();
      // System.out.print("Grounded candidates: ");
      for (Operator o : groundOperator(liftedOperator)) {
        // System.out.print(" " + o);
        List<Argument> grounded = new ArrayList<Argument>();
        List<Argument> free = new ArrayList<Argument>();
        for (int i = 0; i < numParameters; i++) {
          if (isGrounded.test(liftedOperator, liftedOperator.getArguments().get(i))) {
            grounded.add(o.getArguments().get(i));
            free.add(null);
          } else {
            grounded.add(null);
            free.add(o.getArguments().get(i));
          }
        }
        int oNr = operators.size();
        operatorId.put(o, oNr);
        operators.add(o);
        List<List<Integer>> eligibleList = new ArrayList<>();
        List<List<Integer>> parameterSatList = new ArrayList<>();
        for (int i = 0; i < numParameters; i++) {
          List<Integer> arguments = new ArrayList<>();
          List<Integer> satArguments = new ArrayList<>();
          if (!o.getArguments().get(i).isConstant()) {
            List<Argument> args = getConstantsOfType(o.getArguments().get(i).getType());
            for (int j = 0; j < args.size(); j++) {
              arguments.add(constantId.get(args.get(j)));
              satArguments.add(satCounter++);
            }
          }
          eligibleList.add(arguments);
          parameterSatList.add(satArguments);
        }
        eligibleConstants.add(eligibleList);
        parameterSatId.add(parameterSatList);
        operatorSatId.add(satCounter++);
        {
          List<Condition> flatConditions = getFlatConditions(o.getPrecondition());
          for (Condition c : flatConditions) {
            List<Pair<Integer, Integer>> matching = getParamMatching(oNr, c.getArguments());
            for (Condition gc : groundCondition(c)) {
              List<Pair<Integer, Integer>> assignment = new ArrayList<>();
              // boolean valid = true;
              for (Pair<Integer, Integer> match : matching) {
                int argumentIndex = eligibleConstants.get(oNr).get(match.getRight())
                    .indexOf(constantId.get(gc.getArguments().get(match.getLeft())));
                // if (argumentIndex > -1) {
                assignment.add(new Pair<>(match.getRight(), argumentIndex));
                // } else {
                // valid = false;
                // break;
                // }
              }
              // if (!valid) {
              // continue;
              // }
              // if (predicateId.containsKey(gc)) {
              conditionLookup.get(predicateId.get(gc)).get(0).get(gc.isNegated() ? 1 : 0)
                  .add(new Pair<>(oNr, assignment));
              // } else {
              // forbiddenClause.add(new Pair<>(oNr, assignment));
              // }
            }
          }
        }
        {
          List<Condition> flatConditions = getFlatConditions(o.getEffect());
          for (Condition c : flatConditions) {
            List<Pair<Integer, Integer>> matching = getParamMatching(oNr, c.getArguments());
            for (Condition gc : groundCondition(c)) {
              List<Pair<Integer, Integer>> assignment = new ArrayList<>();
              // boolean valid = true;
              for (Pair<Integer, Integer> match : matching) {
                int argumentIndex = eligibleConstants.get(oNr).get(match.getRight())
                    .indexOf(constantId.get(gc.getArguments().get(match.getLeft())));
                // if (argumentIndex > -1) {
                assignment.add(new Pair<>(match.getRight(), argumentIndex));
                // } else {
                // valid = false;
                // break;
                // }
              }
              // if (!valid) {
              // continue;
              // }
              // if (predicateId.containsKey(gc)) {
              conditionLookup.get(predicateId.get(gc)).get(1).get(gc.isNegated() ? 1 : 0)
                  .add(new Pair<>(oNr, assignment));
              // } else {
              // forbiddenClause.add(new Pair<>(oNr, assignment));
              // }
            }
          }
        }

      }
    }
    Logger.log(Logger.INFO, "Number of operators: " + operators.size());

    stepVars = satCounter - 1;
    Logger.log(Logger.INFO, "Number of SAT variables: " + stepVars);
  }

  protected void generateClauses() {
    setInitialState();
    setGoal();
    universalClauses = new ArrayList<>();
    transitionClauses = new ArrayList<>();
    for (int oNr = 0; oNr < operators.size(); oNr++) {
      Operator operator = operators.get(oNr);
      for (int pos = 0; pos < eligibleConstants.get(oNr).size(); pos++) {
        Argument argument = operator.getArguments().get(pos);
        if (argument.isConstant()) {
          continue;
        }
        List<Integer> argumentConstants = eligibleConstants.get(oNr).get(pos);
        {
          // Operator -> each parameter
          int[] clause = new int[argumentConstants.size() + 1];
          clause[0] = -getOperatorNr(oNr);
          for (int cNr = 0; cNr < argumentConstants.size(); cNr++) {
            clause[cNr + 1] = getParameterId(oNr, pos, cNr);
          }
          universalClauses.add(clause);
        }
        {
          // <=1 per Parameter
          // System.out.print("\t<=1 " + argument + ": ");
          for (int c1 = 0; c1 < argumentConstants.size(); c1++) {
            for (int c2 = c1 + 1; c2 < argumentConstants.size(); c2++) {
              int[] clause = new int[2];
              clause[0] = -getParameterId(oNr, pos, c1);
              clause[1] = -getParameterId(oNr, pos, c2);
              universalClauses.add(clause);
            }
          }
        }
      }
    }
    for (int pNr = 0; pNr < predicates.size(); pNr++) {
      for (int condType = 0; condType < 2; condType++) {
        for (int sign = 0; sign < 2; sign++) {
          for (Pair<Integer, List<Pair<Integer, Integer>>> opSupportsPredicate : conditionLookup.get(pNr).get(condType)
              .get(sign)) {
            int oNr = opSupportsPredicate.getLeft();
            int[] clause = new int[2 + opSupportsPredicate.getRight().size()];
            clause[0] = -getOperatorNr(oNr);
            int i = 1;
            for (Pair<Integer, Integer> assignment : opSupportsPredicate.getRight()) {
              clause[i++] = -getParameterId(oNr, assignment.getLeft(), assignment.getRight());
            }
            clause[i++] = (sign == 0 ? 1 : -1) * getPredicateNr(pNr, condType == 1);
            if (condType == 0) {
              universalClauses.add(clause);
            } else {
              transitionClauses.add(clause);
            }
          }
        }
      }
      for (int sign = 0; sign < 2; sign++) {
        for (Pair<Integer, List<Pair<Integer, Integer>>> opHasEffect : conditionLookup.get(pNr).get(1).get(sign)) {
          int effOp = opHasEffect.getLeft();
          for (Pair<Integer, List<Pair<Integer, Integer>>> opHasPrecondition : conditionLookup.get(pNr).get(0)
              .get(1 - sign)) {

            int preOp = opHasPrecondition.getLeft();
            if (effOp == preOp) {
              continue;
            }
            int[] clause = new int[2 + opHasEffect.getRight().size() + opHasPrecondition.getRight().size()];
            clause[0] = -getOperatorNr(effOp);
            clause[1] = -getOperatorNr(preOp);
            int i = 2;
            for (Pair<Integer, Integer> assignment : opHasEffect.getRight()) {
              clause[i++] = -getParameterId(effOp, assignment.getLeft(), assignment.getRight());
            }
            for (Pair<Integer, Integer> assignment : opHasPrecondition.getRight()) {
              clause[i++] = -getParameterId(preOp, assignment.getLeft(), assignment.getRight());
            }
            universalClauses.add(clause);
          }
        }
        {
          List<int[]> frameAxioms = new ArrayList<>();
          frameAxioms.add(new int[2]);
          frameAxioms.get(0)[0] = (sign == 0 ? 1 : -1) * getPredicateNr(pNr, false);
          frameAxioms.get(0)[1] = (sign == 0 ? -1 : 1) * getPredicateNr(pNr, true);
          for (Pair<Integer, List<Pair<Integer, Integer>>> opHasEffect : conditionLookup.get(pNr).get(1).get(sign)) {
            int oNr = opHasEffect.getLeft();
            List<int[]> newFrameAxioms = new ArrayList<>();
            for (int[] oldClause : frameAxioms) {
              {
                int[] clause = new int[oldClause.length + 1];
                System.arraycopy(oldClause, 0, clause, 0, oldClause.length);
                clause[clause.length - 1] = getOperatorNr(oNr);
                newFrameAxioms.add(clause);
              }
              for (Pair<Integer, Integer> assignment : opHasEffect.getRight()) {
                int[] clause = new int[oldClause.length + 1];
                System.arraycopy(oldClause, 0, clause, 0, oldClause.length);
                clause[clause.length - 1] = getParameterId(oNr, assignment.getLeft(), assignment.getRight());
                newFrameAxioms.add(clause);
              }
            }
            frameAxioms = newFrameAxioms;
          }
          transitionClauses.addAll(frameAxioms);
        }
      }
    }
    // for (Pair<Integer, List<Pair<Integer, Integer>>> opHasForbidden :
    // forbiddenClause) {
    // int[] clause = new int[opHasForbidden.getRight().size()];
    // int i = 0;
    // for (Pair<Integer, Integer> assignment : opHasForbidden.getRight()) {
    // clause[i++] = -getParameterId(opHasForbidden.getLeft(), assignment.getLeft(),
    // assignment.getRight());
    // }
    // universalClauses.add(clause);
    // }
    Logger.log(Logger.INFO, "Number of SAT clauses: " + universalClauses.size() + transitionClauses.size());
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

  protected List<Pair<Integer, Integer>> getParamMatching(int oNr, List<Argument> args) {
    Operator o = operators.get(oNr);
    List<Pair<Integer, Integer>> matching = new ArrayList<>();
    for (int i = 0; i < args.size(); i++) {
      Argument a = args.get(i);
      if (!a.isConstant()) {
        matching.add(new Pair<>(i, o.getArguments().indexOf(a)));
      }
    }
    return matching;
  }

  protected List<Condition> getFlatConditions(AbstractCondition ac) {
    List<Condition> result = new ArrayList<>();
    if (ac.getConditionType() == ConditionType.atomic) {
      result.add((Condition) ac);
    } else if (ac.getConditionType() == ConditionType.conjunction) {
      for (AbstractCondition elem : ((ConditionSet) ac).getConditions()) {
        if (elem.getConditionType() != ConditionType.atomic) {
          Logger.log(Logger.ERROR, "Conditionlist not flat: " + ac);
          System.exit(1);
        }
        result.add((Condition) elem);
      }
    } else {
      Logger.log(Logger.ERROR, "Conditionlist not flat: " + ac);
      System.exit(1);
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

  protected int getPredicateNr(int pNr, boolean nextStep) {
    return predicateSatId.get(pNr) + (nextStep ? stepVars : 0);
  }

  protected int getOperatorNr(int oNr) {
    return operatorSatId.get(oNr);
  }

  protected int getParameterId(int oNr, int pos, int cNr) {
    return parameterSatId.get(oNr).get(pos).get(cNr);
  }

  protected void setInitialState() {
    initialClauses = new ArrayList<>();
    Set<Integer> allInitial = new HashSet<Integer>();
    allInitial.addAll(problem.getInitialState().stream().map(c -> predicateId.get(c)).collect(Collectors.toSet()));
    for (int i = 0; i < predicates.size(); i++) {
      if (allInitial.contains(i)) {
        initialClauses.add(new int[] { getPredicateNr(i, false) });
      } else {
        initialClauses.add(new int[] { -getPredicateNr(i, false) });
      }
    }
  }

  protected void nextStep() {
    for (int[] clause : universalClauses) {
      for (int i = 0; i < clause.length; i++) {
        if (clause[i] > 0) {
          clause[i] += stepVars;
        } else {
          clause[i] -= stepVars;
        }
      }
    }
    for (int[] clause : transitionClauses) {
      for (int i = 0; i < clause.length; i++) {
        if (clause[i] > 0) {
          clause[i] += stepVars;
        } else {
          clause[i] -= stepVars;
        }
      }
    }
    for (int i = 0; i < goal.length; i++) {
      if (goal[i] > 0) {
        goal[i] += stepVars;
      } else {
        goal[i] -= stepVars;
      }
    }
  }

  protected void setGoal() {
    if (problem.getGoals().size() != 1) {
      Logger.log(Logger.ERROR, "More than one goal");
      System.exit(1);
    }
    List<Condition> goalConditions = getFlatConditions(problem.getGoals().get(0));
    goal = new int[goalConditions.size()];
    for (int i = 0; i < goalConditions.size(); i++) {
      Condition c = goalConditions.get(i);
      goal[i] = (c.isNegated() ? -1 : 1) * getPredicateNr(predicateId.get(c), false);
    }
  }

  protected PlanningProblem problem;

  protected List<Argument> constants;
  protected Map<Argument, Integer> constantId;
  protected List<Condition> predicates;
  protected Map<Condition, Integer> predicateId;
  protected List<Operator> operators;
  protected Map<Operator, Integer> operatorId;
  // Operator -> Pos -> Constants
  protected List<List<List<Integer>>> eligibleConstants;
  // Predicate -> pre/eff -> pos/neg -> List -> (Operator/List->(pos, nr))
  protected List<List<List<List<Pair<Integer, List<Pair<Integer, Integer>>>>>>> conditionLookup;
  // List -> (Operator/(List->(pos, nr)))
  // protected List<Pair<Integer, List<Pair<Integer, Integer>>>> forbiddenClause;

  protected List<Integer> predicateSatId;
  protected List<Integer> operatorSatId;
  protected List<List<List<Integer>>> parameterSatId;
  protected List<int[]> initialClauses;
  protected List<int[]> universalClauses;
  protected int[] goal;
  protected List<int[]> transitionClauses;
  protected int stepVars;
  protected BiPredicate<Operator, Argument> isGrounded;
}
