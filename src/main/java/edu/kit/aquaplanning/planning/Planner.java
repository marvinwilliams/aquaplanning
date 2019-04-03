package edu.kit.aquaplanning.planning;

import edu.kit.aquaplanning.Configuration;
import edu.kit.aquaplanning.util.Logger;

/**
 * Blueprint for a planner operating on a fully grounded planning problem.
 * 
 * @author Dominik Schreiber
 */
public abstract class Planner {
	
	protected Configuration config;
	protected long searchStartMillis = 0;
    public boolean isGrounded;
	
	public Planner(Configuration config) {
		this.config = config;
	}
	
	protected void startSearch() {
		searchStartMillis = System.currentTimeMillis();
	}
	
	/**
	 * Checks the used amount of iterations and the elapsed time
	 * against computational bounds specified in the configuration.
	 * If false is returned, the planner should stop.
	 */
	protected boolean withinComputationalBounds(int iterations) {
		
		if (Thread.currentThread().isInterrupted())
			return false;
		

		if (config.maxIterations > 0 && iterations >= config.maxIterations) {
			return false;
		}
		
		if (config.searchTimeSeconds > 0) {
			long searchTime = System.currentTimeMillis() - searchStartMillis;
			if (searchTime > config.searchTimeSeconds * 1000) {
				return false;
			}
		}

		if (config.maxTimeSeconds > 0) {
			long totalTime = System.currentTimeMillis() - config.startTimeMillis;
			if (totalTime > config.maxTimeSeconds * 1000) {
				return false;
			}
		}

		return true;
	}

	/**
     * Returns true if the planner is ground, false otherwise
	 */
	public static boolean isGround(Configuration config) {
		
		switch (config.plannerType) {
		case forwardSSS:
          return true;
		case satBased:
          return true;
		case hegemannSat:
          return true;
		case parallel:
          return true;
        case pLiftedSat:
          return false;
        case gLiftedSat:
          return false;
        case hLiftedSat:
          return false;
        case iLiftedSat:
          return false;
        case i2LiftedSat:
          return false;
        case eLiftedSat:
          return false;
		}
		return true;
	}
	
	@Override
	public String toString() {
		return getClass().toString();
	}
}
