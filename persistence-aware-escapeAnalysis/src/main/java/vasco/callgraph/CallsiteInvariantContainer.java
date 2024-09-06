package vasco.callgraph;

import java.util.Map;

import soot.Local;

public class CallsiteInvariantContainer {
	public Map<Integer, Local> paramLocals;
	public PointsToGraph summary;
	
	public CallsiteInvariantContainer(Map<Integer, Local> locals, PointsToGraph entry) {
		this.paramLocals = locals;
		this.summary = entry;
	}
}
