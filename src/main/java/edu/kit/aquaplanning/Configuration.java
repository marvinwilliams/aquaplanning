package edu.kit.aquaplanning;

import edu.kit.aquaplanning.planning.SearchStrategy;
import edu.kit.aquaplanning.util.Logger;
import picocli.CommandLine.Command;
import picocli.CommandLine.Option;
import picocli.CommandLine.Parameters;

/**
 * Bundles all options which can be set for this application.
 */
@Command(mixinStandardHelpOptions = true, version = "Aquaplanning Version 0.0.1-SNAPSHOT")
public class Configuration {
	
	public static final String USAGE_DEFAULT = "(default: @|fg(green) ${DEFAULT-VALUE}|@)";
	public static final String USAGE_OPTIONS_AND_DEFAULT = "@|fg(green) ${COMPLETION-CANDIDATES}|@ "
			+ USAGE_DEFAULT;
	
	
	/* 
	 * General properties and settings 
	 */
	
	/* Input files */
	
	@Parameters(index = "0", paramLabel = "domainFile", 
			description = "Path and name of the PDDL domain file")    
	public String domainFile;
	@Parameters(index = "1", paramLabel = "problemFile", 
			description = "Path and name of the PDDL problem file")    
	public String problemFile;
	
	/* Output files */
	
	@Option(paramLabel = "file", names = "-o", description = "Output plan to file")
	public String planOutputFile;
	
	@Option(paramLabel = "satFile", names = "-SAT", description = "Output SAT formulae to file(s)")
	public String satFormulaFile;
	
	/* Computational bounds */
	
	@Option(paramLabel = "maxIterations", names = {"-m", "--max-iterations"}, 
			description = "Maximum amount of iterations in outer loop "
					+ "of the planning algorithm", defaultValue = "0")
	public int maxIterations;
	
	@Option(paramLabel = "maxSeconds", names = {"-t", "--max-seconds"}, 
			description = "Maximum total runtime in seconds", defaultValue = "0")
	public int maxTimeSeconds;
	
	@Option(paramLabel = "searchSeconds", names = {"-st", "--search-seconds"}, 
			description = "Maximum search time in seconds", defaultValue = "0")
	public int searchTimeSeconds;
	
	@Option(paramLabel = "numThreads", names = {"-T", "--threads"}, 
			description = "The amount of threads to spawn (where applicable)", defaultValue = "1")
	public int numThreads;
	
	/* Output */
	
	@Option(paramLabel = "verbosityLevel", names = {"-v", "--verbosity"}, 
			description = "How verbose output should be "
					+ "(0: errors only, 1: warnings, 2: brief information, etc.) " + USAGE_DEFAULT, 
			defaultValue = (Logger.INFO + ""))
	public int verbosityLevel;
	
	
	
	/*
	 * Preprocessing and grounding configuration
	 */
	
	@Option(names = {"-kd", "--keep-disjunctions"}, description = "Do not compile disjunctive conditions "
			+ "into simple actions, but keep complex logical structure during planning")
	public boolean keepDisjunctions;
	@Option(names = {"-kq", "--keep-equalities"}, description = "Do not resolve equality conditions, "
			+ "but add them as explicit atoms to the initial state")
	public boolean keepEqualities;
	@Option(names = {"-nc", "--no-keep-cond-effects"}, description = "Compile conditional effects "
			+ "into multiple STRIPS operators (implies translation into DNF)")
	public boolean eliminateConditionalEffects;
	
	
	/* 
	 * Planner configuration 
	 */
	
	public enum PlannerType {
		forwardSSS, satBased, hegemannSat, parallel, pLiftedSat, gLiftedSat, hLiftedSat, iLiftedSat, eLiftedSat;
	}
	@Option(paramLabel = "plannerType", names = {"-p", "--planner"}, 
			description = "Planner type to use: " + USAGE_OPTIONS_AND_DEFAULT, 
			defaultValue = "forwardSSS")
	public PlannerType plannerType;
	
	public enum SatSolverType {
        minisat, picosat, glucose;
	}
	@Option(paramLabel = "satSolver", names = {"-ss", "--satsolver"}, 
			description = "Satsolver to use: " + USAGE_OPTIONS_AND_DEFAULT, 
			defaultValue = "minisat")
	public SatSolverType satSolver;
	/* Forward search space planning */
	
	public enum HeuristicType {
		manhattanGoalDistance, relaxedPathLength, actionInterferenceRelaxation, ffTrautmann, ffFroleyks, ffWilliams;
	}
	@Option(paramLabel = "heuristicClass", names = {"-H", "--heuristic"}, 
			description = "Heuristic for forward search: " + USAGE_OPTIONS_AND_DEFAULT, 
			defaultValue = "ffTrautmann")
	public HeuristicType heuristic;
	@Option(paramLabel = "heuristicWeight", names = {"-w", "--heuristic-weight"},
			description = "Weight of heuristic when using a weighted search strategy " + USAGE_DEFAULT, 
			defaultValue = "10")
	public int heuristicWeight;
	
	@Option(paramLabel = "searchStrategy", names = {"-s", "--search"}, 
			description = "Search strategy for forward search: " + USAGE_OPTIONS_AND_DEFAULT, 
			defaultValue = "bestFirst")
	public SearchStrategy.Mode searchStrategy;
	
	@Option(names = {"-r", "--revisit-states"}, description = "Re-enter a search node "
			+ "even when the state has been reached before")
	public boolean revisitStates;
	
	@Option(names = {"-S", "--seed"}, description = "Random seed to use for randomized search strategies",
			defaultValue = "1337")
	public int seed = 1337;
	
	
	/* 
	 * Post-processing 
	 */
	
	@Option(names = {"-O", "--optimize"}, description = "Optimize plan during postprocessing")
	public boolean optimizePlan;
	
	
	/**
	 * currentTimeMillis() time when the application was launched.
	 */
	public long startTimeMillis;
	
	public Configuration() {
		startTimeMillis = System.currentTimeMillis();
	}

	public Configuration copy() {
		
		Configuration config = new Configuration();
		config.domainFile = domainFile;
		config.problemFile = problemFile;
		config.planOutputFile = planOutputFile;
		config.maxIterations = maxIterations;
		config.maxTimeSeconds = maxTimeSeconds;
		config.numThreads = numThreads;
		config.keepDisjunctions = keepDisjunctions;
		config.keepEqualities = keepEqualities;
		config.plannerType = plannerType;
		config.heuristic = heuristic;
		config.heuristicWeight = heuristicWeight;
		config.searchStrategy = searchStrategy;
		config.revisitStates = revisitStates;
		config.seed = seed;
		config.optimizePlan = optimizePlan;
		config.startTimeMillis = startTimeMillis;
		config.searchTimeSeconds = searchTimeSeconds;
		return config;
	}

	@Override
	public String toString() {
		return "Configuration \n domainFile=" + domainFile + "\n problemFile=" + problemFile + "\n planOutputFile="
				+ planOutputFile + "\n maxIterations=" + maxIterations + "\n maxTimeSeconds=" + maxTimeSeconds
				+ "\n searchTimeSeconds=" + searchTimeSeconds + "\n numThreads=" + numThreads + "\n verbosityLevel="
				+ verbosityLevel + "\n keepDisjunctions=" + keepDisjunctions + "\n keepEqualities=" + keepEqualities
				+ "\n plannerType=" + plannerType + "\n heuristic=" + heuristic + "\n heuristicWeight=" + heuristicWeight
				+ "\n searchStrategy=" + searchStrategy + "\n revisitStates=" + revisitStates + "\n seed=" + seed
				+ "\n optimizePlan=" + optimizePlan + "\n startTimeMillis=" + startTimeMillis + "\n";
	}
	
}
