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

  static final class ArgumentMapping {
    public ArgumentMapping(Operator operator, Condition condition) {
      this.operator = operator;
      this.condition = condition.withoutNegation();
      size = 0;
      conditionPos = new ArrayList<>();
      operatorPos = new ArrayList<>();
      refArgs = new ArrayList<>();
      int counter = 0;
      for (int i = 0; i < operator.getArguments().size(); i++) {
        Argument arg = operator.getArguments().get(i);
        if (arg.isConstant()) {
          continue;
        }
        int aIdx = condition.getArguments().indexOf(arg);
        if (aIdx >= 0) {
          conditionPos.add(aIdx);
          operatorPos.add(counter);
          refArgs.add(arg);
          size++;
        }
        counter++;
      }
    }

    public int size() {
      return size;
    }

    public Operator getOperator() {
      return operator;
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

    public Condition getCondition() {
      return condition;
    }

    private int size;
    private List<Argument> refArgs;
    private List<Integer> conditionPos;
    private List<Integer> operatorPos;
    private Condition condition;
    private Operator operator;
  }

  static final class ArgumentAssignment {
    public ArgumentAssignment(ArgumentMapping mapping, List<Argument> conditionArguments) {
      this.mapping = mapping;
      arguments = new ArrayList<>();
      for (int i = 0; i < mapping.size(); i++) {
        arguments.add(conditionArguments.get(mapping.getConditionPos(i)));
      }
      condition = mapping.getCondition().getConditionBoundToArguments(mapping.getRefArgs(), arguments);
    }

    public int size() {
      return arguments.size();
    }

    public ArgumentMapping getMapping() {
      return mapping;
    }

    public Condition getCondition() {
      return condition;
    }

    List<Argument> getArguments() {
      return arguments;
    }

    private Condition condition;
    private ArgumentMapping mapping;
    private List<Argument> arguments;
  }

  static final class ConditionSupport {
    public ConditionSupport() {
      posPreconditions = new HashMap<>();
      negPreconditions = new HashMap<>();
      posEffects = new HashMap<>();
      negEffects = new HashMap<>();
    }

    public void addAssignment(ArgumentAssignment assignment, boolean isNegated, boolean isEffect) {
      Condition condition = assignment.getCondition();
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

    public List<ArgumentAssignment> getAssignments(Condition condition, boolean isNegated, boolean isEffect) {
      Condition c = condition.withoutNegation();
      return isNegated
          ? (isEffect ? negEffects.getOrDefault(c, new ArrayList<>())
              : negPreconditions.getOrDefault(c, new ArrayList<>()))
          : (isEffect ? posEffects.getOrDefault(c, new ArrayList<>())
              : posPreconditions.getOrDefault(c, new ArrayList<>()));
    }

    Map<Condition, List<ArgumentAssignment>> posPreconditions;
    Map<Condition, List<ArgumentAssignment>> negPreconditions;
    Map<Condition, List<ArgumentAssignment>> posEffects;
    Map<Condition, List<ArgumentAssignment>> negEffects;
  }
}
