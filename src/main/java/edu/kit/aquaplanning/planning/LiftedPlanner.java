package edu.kit.aquaplanning.planning;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import edu.kit.aquaplanning.Configuration;
import edu.kit.aquaplanning.grounding.RelaxedPlanningGraph;
import edu.kit.aquaplanning.grounding.RelaxedPlanningGraphGrounder;
import edu.kit.aquaplanning.model.ground.Plan;
import edu.kit.aquaplanning.model.lifted.Argument;
import edu.kit.aquaplanning.model.lifted.Operator;
import edu.kit.aquaplanning.model.lifted.PlanningProblem;
import edu.kit.aquaplanning.model.lifted.condition.Condition;
import edu.kit.aquaplanning.util.Logger;

/**
 * Blueprint for a planner operating on the lifted problem.
 * 
 * @author Dominik Schreiber
 */
public abstract class LiftedPlanner extends Planner {

  public LiftedPlanner(Configuration config) {
    super(config);
    this.isGrounded = false;
  }

  /**
   * Attempt to find a solution plan for the provided problem.
   */
  public abstract Plan findPlan(PlanningProblem problem);

  public static LiftedPlanner getPlanner(Configuration config) {
    switch (config.plannerType) {
    case pLiftedSat:
      return new PureLiftedSatPlanner(config);
    case gLiftedSat:
      return new GroundLiftedSatPlanner(config);
    case hLiftedSat:
      return new HelperLiftedSatPlanner(config);
    case iLiftedSat:
      return new IsolateLiftedSatPlanner(config);
    default:
      return null;
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
    for (int i = 0; i < goalClause.length; i++) {
      if (goalClause[i] > 0) {
        goalClause[i] += stepVars;
      } else {
        goalClause[i] -= stepVars;
      }
    }
  }

  public ParameterMatching getParameterMatching(Operator o, Condition c) {
    int operatorId = operators.get(o);
    List<Integer> predicatePos = new ArrayList<>();
    List<Integer> operatorPos = new ArrayList<>();
    for (int i = 0; i < c.getArguments().size(); i++) {
      Argument a = c.getArguments().get(i);
      if (!a.isConstant()) {
        predicatePos.add(i);
        operatorPos.add(o.getArguments().indexOf(a));
      }
    }
    return new ParameterMatching(operatorId, predicatePos, operatorPos);
  }

  class ParameterMatching {
    int operatorId;
    List<Integer> predicatePos;
    List<Integer> operatorPos;

    public ParameterMatching(int operatorId, List<Integer> predicatePos, List<Integer> operatorPos) {
      this.operatorId = operatorId;
      this.predicatePos = predicatePos;
      this.operatorPos = operatorPos;
    }

    public int size() {
      return predicatePos.size();
    }

    public int getPredicatePos(int i) {
      return predicatePos.get(i);
    }

    public int getOperatorPos(int i) {
      return operatorPos.get(i);
    }

    public int getArgumentId(Condition c, int i) {
      return eligibleArguments.get(operatorId).get(getOperatorPos(i)).get(c.getArguments().get(getPredicatePos(i)));
    }

    public int getOperatorId() {
      return operatorId;
    }
  }

  class Assignment {
    public int operatorId;
    public List<Integer> position;
    public List<Integer> argumentId;

    public Assignment(int operatorId, List<Integer> position, List<Integer> argumentId) {
      this.operatorId = operatorId;
      this.position = position;
      this.argumentId = argumentId;
    }

    public int size() {
      return position.size();
    }

    public int getOperatorId() {
      return operatorId;
    }

    public int getPosition(int i) {
      return position.get(i);
    }

    public int getArgumentId(int i) {
      return argumentId.get(i);
    }

    @Override
    public String toString() {
      return "Operator " + operatorId + ": " + position + "|" + argumentId;
    }

    @Override
    public int hashCode() {
      final int prime = 31;
      int result = 1;
      result = prime * result + operatorId;
      result = prime * result + position.hashCode();
      result = prime * result + argumentId.hashCode();
      return result;
    }

    @Override
    public boolean equals(Object other) {
      if (this == other) {
        return true;
      }
      if (other == null) {
        return false;
      }
      if (other.getClass() != getClass()) {
        return false;
      }
      Assignment tmp = (Assignment) other;
      if (operatorId != tmp.operatorId) {
        return false;
      }
      if (!position.equals(tmp.position)) {
        return false;
      }
      if (!argumentId.equals(tmp.argumentId)) {
        return false;
      }
      return true;
    }
  }

  protected List<int[]> DNF2CNF(List<int[]> dnf) {
    List<int[]> result = new ArrayList<>();
    DNF2CNF(dnf, 0, result, new int[dnf.size()]);
    return result;
  }

  protected void DNF2CNF(List<int[]> dnf, int depth, List<int[]> result, int[] current) {
    if (depth == dnf.size()) {
      result.add(current);
    } else {
      for (int i : dnf.get(depth)) {
        int[] tmp = current.clone();
        tmp[depth] = i;
        DNF2CNF(dnf, depth + 1, result, tmp);
      }
    }
  }

  class Solution {
    int[] model;
    int steps;
  }

  protected Solution incPlan() {
    Solution solution = new Solution();
    solution.steps = -1;
    try {
      File file = File.createTempFile("cnf", ".cnf");
      // file.deleteOnExit();
      FileWriter writer = new FileWriter(file);
      {
        String header = "i cnf " + stepVars + " " + initialClauses.size() + "\n";
        writer.write(header);
        for (int[] clause : initialClauses) {
          String line = Arrays.stream(clause).mapToObj(String::valueOf).collect(Collectors.joining(" "));
          line += " 0\n";
          writer.write(line);
        }
      }
      {
        String header = "u cnf " + stepVars + " " + universalClauses.size() + "\n";
        writer.write(header);
        for (int[] clause : universalClauses) {
          String line = Arrays.stream(clause).mapToObj(String::valueOf).collect(Collectors.joining(" "));
          line += " 0\n";
          writer.write(line);
        }
      }
      {
        String header = "g cnf " + stepVars + " " + goalClause.length + "\n";
        writer.write(header);
        for (int g : goalClause) {
          String line = g + " 0\n";
          writer.write(line);
        }
      }
      {
        String header = "t cnf " + 2 * stepVars + " " + transitionClauses.size() + "\n";
        writer.write(header);
        for (int[] clause : transitionClauses) {
          String line = Arrays.stream(clause).mapToObj(String::valueOf).collect(Collectors.joining(" "));
          line += " 0\n";
          writer.write(line);
        }
      }
      writer.close();
      Runtime run = Runtime.getRuntime();
      Logger.log(Logger.INFO, "TIME2 Running incplan");
      Process proc = run.exec("./incplan-minisat220 " + file.getPath());
      proc.waitFor();
      Logger.log(Logger.INFO, "TIME3 Finished");
      BufferedReader reader = new BufferedReader(new InputStreamReader(proc.getInputStream()));
      String outline;
      int numSteps = -1;
      int numVars = -1;
      while ((outline = reader.readLine()) != null) {
        if (outline.startsWith("solution")) {
          numVars = Integer.valueOf(outline.split(" ")[1]);
          numSteps = Integer.valueOf(outline.split(" ")[2]);
          break;
        }
      }
      int[] model = new int[numVars * numSteps + 1];
      int stepCounter = 0;
      int i = 1;
      while ((outline = reader.readLine()) != null) {
        if (stepCounter == numSteps) {
          break;
        }
        // System.out.println(outline);
        for (String vStr : outline.split(" ")) {
          int v = Integer.valueOf(vStr);
          model[i++] = v;
        }
        stepCounter++;
      }
      solution.steps = numSteps;
      solution.model = model;
    } catch (Exception e) {
      Logger.log(Logger.ERROR, "Error calling external program");
    }
    return solution;
  }

  @Override
  public String toString() {
    return getClass().toString();
  }

  protected PlanningProblem problem;
  protected RelaxedPlanningGraph graph;
  protected RelaxedPlanningGraphGrounder grounder;

  protected Map<Condition, Integer> predicates;
  protected Map<Operator, Integer> operators;
  protected List<List<Map<Argument, Integer>>> eligibleArguments;

  protected List<Set<Assignment>> preconditionsPos;
  protected List<Set<Assignment>> preconditionsNeg;
  protected List<Set<Assignment>> effectsPos;
  protected List<Set<Assignment>> effectsNeg;
  protected Set<Assignment> forbidden;

  protected List<int[]> initialClauses;
  protected List<int[]> universalClauses;
  protected int[] goalClause;
  protected List<int[]> transitionClauses;
  protected int stepVars;
}
