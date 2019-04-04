package edu.kit.aquaplanning.planning;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.kit.aquaplanning.Configuration;
import edu.kit.aquaplanning.grounding.ArgumentCombinationUtils;
import edu.kit.aquaplanning.grounding.RelaxedPlanningGraphGrounder;
import edu.kit.aquaplanning.model.ground.Plan;
import edu.kit.aquaplanning.model.lifted.Argument;
import edu.kit.aquaplanning.model.lifted.Operator;
import edu.kit.aquaplanning.model.lifted.PlanningProblem;
import edu.kit.aquaplanning.model.lifted.Type;
import edu.kit.aquaplanning.model.lifted.condition.AbstractCondition;
import edu.kit.aquaplanning.model.lifted.condition.AbstractCondition.ConditionType;
import edu.kit.aquaplanning.sat.SatSolver;
import edu.kit.aquaplanning.model.lifted.condition.Condition;
import edu.kit.aquaplanning.model.lifted.condition.ConditionSet;
import edu.kit.aquaplanning.util.Logger;
import edu.kit.aquaplanning.util.Pair;

public class ExistsLiftedSatPlanner extends LiftedPlanner {

  public ExistsLiftedSatPlanner(Configuration config) {
    super(config);
  }

  @Override
  public Plan findPlan(PlanningProblem p) {
    problem = p;
    Logger.log(Logger.INFO, "TIME0 Grounding");
    grounder = new RelaxedPlanningGraphGrounder(config);
    graph = grounder.computeGraph(p);
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

//   for (int[] clause : initialClauses) {
//     solver.addClause(clause);
//   }
//   Logger.log(Logger.INFO, "TIME2 Starting solver");
//   int step = 0;
//   while (true) {
//     for (int[] clause : universalClauses) {
//       solver.addClause(clause);
//     }
//     if (solver.isSatisfiable(goalClause)) {
//       Logger.log(Logger.INFO, "TIME3 Solution found in step " + step);
//       break;
//     }
//     Logger.log(Logger.INFO, "No solution found in step " + step);
//     for (int[] clause : transitionClauses) {
//       solver.addClause(clause);
//     }
//     nextStep();
//     step++;
//   }
    grounder.ground(problem);
 //   return extractPlan(solver.getModel(), step);
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
  }

  protected Plan extractPlan(int[] model, int steps) {
    Plan plan = new Plan();
    for (int base = 0; base < steps * stepVars; base += stepVars) {
   //   System.out.println("New step");
      List<List<Operator>> stepPlan = new ArrayList<>();
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
     //     System.out.println("Added " + go);
          stepPlan.add(Arrays.asList(o, go));
        }
      }
      stepPlan.sort((a, b) -> operators.get(a.get(0)) - operators.get(b.get(0)));
      for (List<Operator> operatorPair: stepPlan) {
        plan.appendAtBack(grounder.getAction(operatorPair.get(1)));
      }
    }
    return plan;
  }

  protected void computeGrounding(Operator o, List<Set<Argument>> args) {
    List<Integer> groundPos = new ArrayList<>();
    int best = -1;
    for (int i = 0; i <= o.getArguments().size(); i++) {
      int tmp = computeGrounding(o, i, groundPos, 0, best, args);
      if (tmp > -1 && (tmp < best || best == -1)) {
        best = tmp;
      }
    }
  }

  protected int computeGrounding(Operator o, int numArgs, List<Integer> current, int pos, int oldBest,
      List<Set<Argument>> args) {
    if (numArgs == 0) {
      int res = testGrounding(o, current, args);
      if (res > -1 && (res < oldBest || oldBest < 0)) {
        operatorGrounding.put(o, current);
        return res;
      }
      return -1;
    }
    while (pos + numArgs <= o.getArguments().size()) {
      if (!o.getArguments().get(pos).isConstant()) {
        List<Integer> tmp = new ArrayList<>(current);
        tmp.add(pos);
        int res = computeGrounding(o, numArgs - 1, tmp, pos + 1, oldBest, args);
        if (res > -1 && (res < oldBest || oldBest < 0)) {
          oldBest = res;
        }
      }
      pos++;
    }
    return oldBest;
  }

  protected int testGrounding(Operator o, List<Integer> groundPos, List<Set<Argument>> args) {
    List<Argument> tmpArgs = new ArrayList<>();
    for (int i = 0; i < o.getArguments().size(); i++) {
      tmpArgs.add(null);
    }
    int numOperators = 1;
    for (int i = 0; i < groundPos.size(); i++) {
      tmpArgs.set(groundPos.get(i), new Argument("test", new Type("test")));
      if (groundPos.get(i) != null) {
        numOperators *= args.get(groundPos.get(i)).size();
      }
    }
    Operator groundedOperator = o.getOperatorWithGroundArguments(tmpArgs);
    AbstractCondition ac = groundedOperator.getEffect();
    ConditionSet simpleSet = grounder.splitCondition(ac).getLeft();
    for (AbstractCondition c : simpleSet.getConditions()) {
      if (c.getConditionType() != ConditionType.atomic) {
        // Logger.log(Logger.WARN, "A simple set of conditions contains non-atomic
        // condition " + c + ".");
        // Logger.log(Logger.WARN, "These conditions will be ignored");
        // System.exit(1);
        continue;
      }
      Condition condition = (Condition) c;
      boolean hasVariable = false;
      for (Argument a : condition.getArguments()) {
        if (!a.isConstant()) {
          if (hasVariable) {
            return -1;
          } else {
            hasVariable = true;
          }
        }
      }
    }
    // System.out.println("Lifted: " + o);
    // System.out.println("Grounded: " + groundedOperator);
    return numOperators;
  }

  protected void initIDs() {
    satCounter = 1;
    constants = problem.getConstants();
    setPredicateIDs();
    setOperatorIDs();
    forbidden = new HashSet<>();
    for (Operator operator : operators.keySet()) {
      for (AbstractCondition ac : Arrays.asList(operator.getPrecondition(), operator.getEffect())) {
        Pair<ConditionSet, ConditionSet> split = grounder.splitCondition(ac);
        ConditionSet simpleSet = split.getLeft();
        for (AbstractCondition c : split.getRight().getConditions()) {
          if (c.getConditionType() != ConditionType.numericEffect) {
            Logger.log(Logger.ERROR, "Condition contains complex set: " + split);
            System.exit(1);
          }
        }
        for (AbstractCondition c : simpleSet.getConditions()) {
          if (c.getConditionType() != ConditionType.atomic) {
            // Logger.log(Logger.WARN, "A simple set of conditions contains non-atomic
            // condition " + c + ".");
            // Logger.log(Logger.WARN, "These conditions will be ignored");
            // System.exit(1);
            continue;
          }
          Condition condition = (Condition) c;
          setForbiddenConditions(operator, condition);
        }
      }
    }
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
    rigidConditions = new HashSet<>();
    chainImpliesPos = new ArrayList<>();
    chainImpliesNeg = new ArrayList<>();
    implyChainPos = new ArrayList<>();
    implyChainNeg = new ArrayList<>();
    chainPosSatId = new ArrayList<>();
    chainNegSatId = new ArrayList<>();
    for (Condition p : graph.getLiftedState(graph.getCurrentLayer())) {
      // System.out.println(p);
      predicates.put(p, predicates.size());
      predicateSatId.add(satCounter++);
      preconditionsPos.add(new HashSet<>());
      preconditionsNeg.add(new HashSet<>());
      effectsPos.add(new HashSet<>());
      effectsNeg.add(new HashSet<>());
      chainImpliesPos.add(new ArrayList<>());
      chainImpliesNeg.add(new ArrayList<>());
      implyChainPos.add(new ArrayList<>());
      implyChainNeg.add(new ArrayList<>());
      chainPosSatId.add(new ArrayList<>());
      chainNegSatId.add(new ArrayList<>());
    }
  }

  protected void setOperatorIDs() {
    operators = new HashMap<>();
    operatorSatId = new ArrayList<>();
    parameterSatId = new ArrayList<>();
    eligibleArguments = new ArrayList<>();
    operatorGrounding = new HashMap<>();
    Map<String, Operator> operatorLookup = new HashMap<>();
    List<List<Set<Argument>>> liftedOperatorArguments = new ArrayList<>();
    List<Set<Integer>> operatorEffectsPos = new ArrayList<>();
    List<Set<Integer>> operatorEffectsNeg = new ArrayList<>();
    List<Set<Integer>> operatorPreconditionsPos = new ArrayList<>();
    List<Set<Integer>> operatorPreconditionsNeg = new ArrayList<>();
    for (Operator o : problem.getOperators()) {
      operatorLookup.put(o.getName(), o);
      liftedOperatorArguments.add(new ArrayList<>());
      for (int i = 0; i < o.getArguments().size(); i++) {
        liftedOperatorArguments.get(liftedOperatorArguments.size() - 1).add(new HashSet<>());
      }
    }
    for (Operator o : graph.getLiftedActions()) {
      Operator liftedOperator = operatorLookup.get(o.getName());
      for (int i = 0; i < o.getArguments().size(); i++) {
        liftedOperatorArguments.get(problem.getOperators().indexOf(liftedOperator)).get(i).add(o.getArguments().get(i));
      }
    }
    for (int i = 0; i < problem.getOperators().size(); i++) {
      computeGrounding(problem.getOperators().get(i), liftedOperatorArguments.get(i));
    }
    for (Operator groundedOperator : graph.getLiftedActions()) {
      // System.out.println(groundedOperator);
      Operator liftedOperator = operatorLookup.get(groundedOperator.getName());
      int numParameters = groundedOperator.getArguments().size();
      List<Integer> groundPos = operatorGrounding.get(liftedOperator);
      List<Argument> args = new ArrayList<>();
      for (int i = 0; i < numParameters; i++) {
        args.add(null);
      }
      for (int i = 0; i < groundPos.size(); i++) {
        args.set(groundPos.get(i), groundedOperator.getArguments().get(groundPos.get(i)));
      }
      Operator newOperator = liftedOperator.getOperatorWithGroundArguments(args);
      Integer operatorId = operators.get(newOperator);
      if (operatorId == null) {
        // computeGrounding(newOperator);
        operatorId = operators.size();
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
          }
        }
        parameterSatId.add(satId);
        eligibleArguments.add(operatorArguments);
        operatorEffectsPos.add(new HashSet<>());
        operatorEffectsNeg.add(new HashSet<>());
        operatorPreconditionsPos.add(new HashSet<>());
        operatorPreconditionsNeg.add(new HashSet<>());
      }
      for (int i = 0; i < numParameters; i++) {
        if (newOperator.getArguments().get(i).isConstant()) {
          continue;
        }
        Map<Argument, Integer> knownArguments = eligibleArguments.get(operatorId).get(i);
        Argument argument = groundedOperator.getArguments().get(i);
        if (!knownArguments.containsKey(argument)) {
          // System.out.println("New argument for " + operatorId + " at pos " + i + ": " +
          // argument);
          knownArguments.put(argument, knownArguments.size());
          parameterSatId.get(operatorId).get(i).add(satCounter++);
        }
      }
      for (boolean isPrecondition : Arrays.asList(true, false)) {
        Pair<ConditionSet, ConditionSet> split = isPrecondition ? grounder.splitCondition(newOperator.getPrecondition())
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
          Condition groundCondition = condition.getConditionBoundToArguments(newOperator.getArguments(),
              groundedOperator.getArguments());

          if (predicates.get(groundCondition.withoutNegation()) == null) {
            // // rigid
            rigidConditions.add(groundCondition.withoutNegation());
            // System.out.println("Rigid: " + groundCondition.withoutNegation());
            continue;
          }
          int pId = predicates.get(groundCondition.withoutNegation());
          List<Integer> position = new ArrayList<>();
          List<Integer> argumentId = new ArrayList<>();
          // System.out.println("for operator " + newOperator);
          // System.out.println("Arguments: " + eligibleArguments.get(operatorId));
          // System.out.println("Predicate: " + precondition);
          // System.out.println("GroundPredicate: " + groundPrecondition);
          for (int i = 0; i < matching.size(); i++) {
            position.add(matching.getOperatorPos(i));
            argumentId.add(matching.getArgumentId(groundCondition, i));
          }
          // System.out.println("Positions: " + position);
          // System.out.println("Ids: " + argumentId);
          Assignment assignment = new Assignment(operatorId, position, argumentId);
          if (groundCondition.isNegated()) {
            if (!rigidConditions.contains(groundCondition.withoutNegation())) {
              if (isPrecondition) {
                preconditionsNeg.get(pId).add(assignment);
                operatorPreconditionsNeg.get(operatorId).add(pId);
              } else {
                effectsNeg.get(pId).add(assignment);
                operatorEffectsNeg.get(operatorId).add(pId);
              }
            }
          } else {
            if (!rigidConditions.contains(groundCondition)) {
              if (isPrecondition) {
                preconditionsPos.get(pId).add(assignment);
                operatorPreconditionsPos.get(operatorId).add(pId);
              } else {
                effectsPos.get(pId).add(assignment);
                operatorEffectsPos.get(operatorId).add(pId);
              }
            }
          }
        }
      }
    }
    for (int oId = 0; oId < operators.size(); oId++) {
      for (int pId : operatorPreconditionsPos.get(oId)) {
        if (!chainImpliesNeg.get(pId).isEmpty()) {
          if (chainImpliesNeg.get(pId).get(chainImpliesNeg.get(pId).size() - 1).isEmpty()) {
            chainNegSatId.get(pId).add(satCounter++);
          }
          chainImpliesNeg.get(pId).get(chainImpliesNeg.get(pId).size() - 1).add(oId);
        }
      }
      for (int pId : operatorPreconditionsNeg.get(oId)) {
        if (!chainImpliesPos.get(pId).isEmpty()) {
          if (chainImpliesPos.get(pId).get(chainImpliesPos.get(pId).size() - 1).isEmpty()) {
            chainPosSatId.get(pId).add(satCounter++);
          }
          chainImpliesPos.get(pId).get(chainImpliesPos.get(pId).size() - 1).add(oId);
        }
      }
      for (int pId : operatorEffectsPos.get(oId)) {
        if (chainImpliesPos.get(pId).isEmpty() || !chainImpliesPos.get(pId).get(chainImpliesPos.get(pId).size() - 1).isEmpty()) {
          chainImpliesPos.get(pId).add(new ArrayList<>());
          implyChainPos.get(pId).add(new ArrayList<>());
        }
        implyChainPos.get(pId).get(implyChainPos.get(pId).size() - 1).add(oId);
      }
      for (int pId : operatorEffectsNeg.get(oId)) {
        if (chainImpliesNeg.get(pId).isEmpty() || !chainImpliesNeg.get(pId).get(chainImpliesNeg.get(pId).size() - 1).isEmpty()) {
          chainImpliesNeg.get(pId).add(new ArrayList<>());
          implyChainNeg.get(pId).add(new ArrayList<>());
        }
        implyChainNeg.get(pId).get(implyChainNeg.get(pId).size() - 1).add(oId);
      }
    }
   //System.out.println("Activate Chain:");
   //System.out.println(implyChainPos);
   //System.out.println(implyChainNeg);
   //System.out.println("Chain activates");
   //System.out.println(chainImpliesPos);
   //System.out.println(chainImpliesNeg);
    // System.out.println("Preconditions: " + preconditionsPos);
    // System.out.println("");
    // System.out.println(preconditionsNeg);
    // System.out.println("Effects: " + effectsPos);
    // System.out.println("");
    // System.out.println(effectsNeg);
    // System.out.println(operatorGrounding);
  }

  protected void setForbiddenConditions(Operator o, Condition c) {
    ParameterMatching matching = getParameterMatching(o, c);
    List<Argument> variableParameters = new ArrayList<>();
    List<List<Argument>> eligible = new ArrayList<>();
    for (int i = 0; i < matching.size(); i++) {
      variableParameters.add(c.getArguments().get(matching.getPredicatePos(i)));
      eligible.add(
          new ArrayList<>(eligibleArguments.get(matching.getOperatorId()).get(matching.getOperatorPos(i)).keySet()));
    }
    ArgumentCombinationUtils.iterator(eligible).forEachRemaining(args -> {
      Condition groundCondition = c.getConditionBoundToArguments(variableParameters, args);
      if (!predicates.containsKey(groundCondition.withoutNegation())
          && !rigidConditions.contains(groundCondition.withoutNegation())) {
        // System.out.println("Forbidden for operator " + operators.get(o) + ": " +
        // args);
        List<Integer> position = new ArrayList<>();
        List<Integer> argumentId = new ArrayList<>();
        for (int i = 0; i < matching.size(); i++) {
          position.add(matching.getOperatorPos(i));
          argumentId.add(matching.getArgumentId(groundCondition, i));
        }
        forbidden.add(new Assignment(matching.getOperatorId(), position, argumentId));
      }
    });
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
    numClauses = addImplicationChain();
    Logger.log(Logger.INFO, "Implication chain: " + numClauses);
    numClauses = addFrameAxioms();
    Logger.log(Logger.INFO, "Frame axioms: " + numClauses);
    numClauses = addForbiddenClauses();
    Logger.log(Logger.INFO, "Forbidden clauses: " + numClauses);
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
          // Operator -> Parameter
          int[] clause = new int[numArgs + 1];
          int counter = 0;
          clause[counter++] = -getOperatorSatId(oId);
          for (int aId : arguments.values()) {
            clause[counter++] = getParameterSatId(oId, pos, aId);
          }
          universalClauses.add(clause);
          numClauses++;
        }
        {
          // Parameter -> Operator
          for (int aId : arguments.values()) {
            int[] clause = new int[2];
            clause[0] = -getParameterSatId(oId, pos, aId);
            clause[1] = getOperatorSatId(oId);
            universalClauses.add(clause);
            numClauses++;
          }
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
            int[] clause = new int[Math.max(assignment.size(), 1) + 1];
            if (assignment.size() >= 1) {
              int counter = 0;
              for (int i = 0; i < assignment.size(); i++) {
                clause[counter++] = -getParameterSatId(oId, assignment.getPosition(i), assignment.getArgumentId(i));
              }
              clause[counter++] = (isPositive ? 1 : -1) * getPredicateSatId(pId, !isPrecondition);
            } else {
              clause = new int[2];
              clause[0] = -getOperatorSatId(oId);
              clause[1] = (isPositive ? 1 : -1) * getPredicateSatId(pId, !isPrecondition);
            }
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

  protected int addImplicationChain() {
    int numClauses = 0;
    for (int pId : predicates.values()) {
      for (boolean isPositive : Arrays.asList(true, false)) {
        // System.out.println("Condition: " + c);
        Set<Assignment> support;
        List<List<Integer>> chainImplies;
        List<List<Integer>> implyChain;
        List<Integer> chainSatId;
        if (isPositive) {
          support = effectsPos.get(pId);
          chainImplies = chainImpliesPos.get(pId);
          implyChain = implyChainPos.get(pId);
          chainSatId = chainPosSatId.get(pId);
        } else {
          support = effectsNeg.get(pId);
          chainImplies = chainImpliesNeg.get(pId);
          implyChain = implyChainNeg.get(pId);
          chainSatId = chainNegSatId.get(pId);
        }
        for (int i = 0; i < chainSatId.size() - 1; i++) {
          int[] clause = new int[2];
          clause[0] = -chainSatId.get(i);
          clause[1] = chainSatId.get(i + 1);
          universalClauses.add(clause);
          numClauses++;
        }
        for (int i = 0; i < chainSatId.size(); i++) {
          for (int oId : implyChain.get(i)) {
            int[] clause = new int[2];
            clause[0] = -getOperatorSatId(oId);
            clause[1] = chainSatId.get(i);
            universalClauses.add(clause);
            numClauses++;
          }
        }
        for (int i = 0; i < chainSatId.size(); i++) {
          for (int oId : chainImplies.get(i)) {
            int[] clause = new int[2];
            clause[0] = -chainSatId.get(i);
            clause[1] = -getOperatorSatId(oId);
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
        int[] clause = new int[support.size() + 2];
        int counter = 0;
        clause[counter++] = (isPositive ? 1 : -1) * getPredicateSatId(pId, false);
        clause[counter++] = (isPositive ? -1 : 1) * getPredicateSatId(pId, true);
        for (Assignment assignment : support) {
          if (assignment.size() > 1) {
            Logger.log(Logger.ERROR, "Support for predicate " + pId + " is not unary: " + assignment.getOperatorId());
            System.exit(1);
          }
          if (assignment.size() == 1) {
            clause[counter++] = getParameterSatId(assignment.getOperatorId(), assignment.getPosition(0),
                assignment.getArgumentId(0));
          } else {
            clause[counter++] = getOperatorSatId(assignment.getOperatorId());
          }
        }
        transitionClauses.add(clause);
        numClauses++;
      }
    }
    return numClauses;
  }

  protected int addForbiddenClauses() {
    int numClauses = 0;
    for (Assignment assignment : forbidden) {
      int oNr = assignment.getOperatorId();
      int[] clause = new int[assignment.size()];
      int counter = 0;
      for (int i = 0; i < assignment.size(); i++) {
        clause[counter++] = -getParameterSatId(oNr, assignment.getPosition(i), assignment.getArgumentId(i));
      }
      universalClauses.add(clause);
      numClauses++;
    }
    return numClauses;
  }

  protected void setGoal() {
    ConditionSet goalSet = new ConditionSet(ConditionType.conjunction);
    problem.getGoals().forEach(c -> goalSet.add(c));
    Pair<ConditionSet, ConditionSet> split = grounder.splitCondition(goalSet);
    ConditionSet simpleSet = split.getLeft();
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

  protected int getPredicateSatId(int pId, boolean nextStep) {
    return predicateSatId.get(pId) + (nextStep ? stepVars : 0);
  }

  protected int getOperatorSatId(int oId) {
    return operatorSatId.get(oId);
  }

  protected int getParameterSatId(int oId, int pos, int cId) {
    return parameterSatId.get(oId).get(pos).get(cId);
  }

  protected List<Set<Integer>> hasSeenEffectPos;
  protected List<Set<Integer>> hasSeenEffectNeg;
  protected List<Set<Integer>> hasSeenPreconditionPos;
  protected List<Set<Integer>> hasSeenPreconditionNeg;
  protected List<List<List<Integer>>> chainImpliesPos;
  protected List<List<List<Integer>>> chainImpliesNeg;
  protected List<List<List<Integer>>> implyChainPos;
  protected List<List<List<Integer>>> implyChainNeg;
  protected List<List<Integer>> chainPosSatId;
  protected List<List<Integer>> chainNegSatId;
  protected List<Argument> constants;
  protected Map<Operator, List<Integer>> operatorGrounding;
  protected List<Integer> predicateSatId;
  protected List<Integer> operatorSatId;
  protected List<List<List<Integer>>> parameterSatId;
  protected Set<Condition> rigidConditions;

  protected int satCounter;
}
