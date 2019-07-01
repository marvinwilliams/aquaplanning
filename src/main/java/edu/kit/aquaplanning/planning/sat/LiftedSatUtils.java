package edu.kit.aquaplanning.planning.sat;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.kit.aquaplanning.model.lifted.Argument;
import edu.kit.aquaplanning.model.lifted.Operator;
import edu.kit.aquaplanning.model.lifted.condition.Condition;

public final class LiftedSatUtils {
  private LiftedSatUtils() {
  }

  public static class ArgumentMapping {
    public ArgumentMapping(Operator operator, Condition condition) {
      this.operator = operator;
      this.condition = condition.withoutNegation();
      size = 0;
      conditionPos = new ArrayList<>();
      operatorPos = new ArrayList<>();
      refArgs = new ArrayList<>();
      for (int i = 0; i < condition.getNumArgs(); i++) {
        Argument arg = condition.getArguments().get(i);
        if (arg.isConstant()) {
          continue;
        }
        int counter = 0;
        for (Argument oArg : operator.getArguments()) {
          if (oArg.isConstant()) {
            continue;
          }
          if (oArg.equals(arg)) {
            operatorPos.add(counter);
            conditionPos.add(i);
            refArgs.add(arg);
            size++;
            break;
          }
          counter++;
        }
      }
    }

    public int size() {
      return size;
    }

    public Operator getOperator() {
      return operator;
    }

    public Condition getCondition() {
      return condition;
    }

    public int getConditionPos(int i) {
      return conditionPos.get(i);
    }

    public int getOperatorPos(int i) {
      return operatorPos.get(i);
    }

    public List<Argument> getRefArgs() {
      return refArgs;
    }

    private int size;
    private List<Argument> refArgs;
    private List<Integer> conditionPos;
    private List<Integer> operatorPos;
    private Condition condition;
    private Operator operator;
  }

  public static final class ArgumentAssignment extends ArgumentMapping {
    public ArgumentAssignment(Operator operator, Condition condition,
        List<Argument> conditionArguments) {
      super(operator, condition);
      arguments = new ArrayList<>();
      for (int i = 0; i < size(); i++) {
        arguments.add(conditionArguments.get(i));
      }
      groundedCondition = getCondition()
          .getConditionBoundToArguments(getRefArgs(), arguments);
    }

    public Condition getGroundedCondition() {
      return groundedCondition;
    }

    List<Argument> getArguments() {
      return arguments;
    }

    private Condition groundedCondition;
    private List<Argument> arguments;
  }

  public static final class ConditionSupport {
    public ConditionSupport() {
      posPreconditions = new HashMap<>();
      negPreconditions = new HashMap<>();
      posEffects = new HashMap<>();
      negEffects = new HashMap<>();
    }

    public void addAssignment(ArgumentAssignment assignment, boolean isNegated,
        boolean isEffect) {
      Condition condition = assignment.getGroundedCondition();
      if (isEffect) {
        if (isNegated) {
          negEffects.putIfAbsent(condition, new ArrayList<>());
          negEffects.get(condition).add(assignment);
        } else {
          posEffects.putIfAbsent(condition, new ArrayList<>());
          posEffects.get(condition).add(assignment);
        }
      } else {
        if (isNegated) {
          negPreconditions.putIfAbsent(condition, new ArrayList<>());
          negPreconditions.get(condition).add(assignment);
        } else {
          posPreconditions.putIfAbsent(condition, new ArrayList<>());
          posPreconditions.get(condition).add(assignment);
        }
      }
    }

    public List<ArgumentAssignment> getAssignments(Condition condition,
        boolean isNegated, boolean isEffect) {
      return isNegated
          ? (isEffect ? negEffects.getOrDefault(condition, new ArrayList<>())
              : negPreconditions.getOrDefault(condition, new ArrayList<>()))
          : (isEffect ? posEffects.getOrDefault(condition, new ArrayList<>())
              : posPreconditions.getOrDefault(condition, new ArrayList<>()));
    }

    private Map<Condition, List<ArgumentAssignment>> posPreconditions;
    private Map<Condition, List<ArgumentAssignment>> negPreconditions;
    private Map<Condition, List<ArgumentAssignment>> posEffects;
    private Map<Condition, List<ArgumentAssignment>> negEffects;
  }

  public static final class Clause {
    public Clause() {
      varList = new ArrayList<>();
    }

    public void add(int satVar) {
      varList.add(satVar);
    }

    public void add(Clause clause) {
      varList.addAll(clause.varList);
    }

    public void add(List<Integer> satVars) {
      varList.addAll(satVars);
    }

    public int[] toArray() {
      return varList.stream().mapToInt(x -> x).toArray();
    }

    private List<Integer> varList;
  }
}
