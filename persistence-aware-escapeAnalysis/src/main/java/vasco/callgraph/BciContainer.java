package vasco.callgraph;

public class BciContainer {
	public BciContainer(int ci, int bci) {
		this.bci = bci;
		this.callerIndex = ci;
	}
	private int callerIndex;
	private int bci;
	public int getCallerIndex() {
		return callerIndex;
	}
	public int getBci() {
		return bci;
	}
	
	public Type type;
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(callerIndex).append("-").append(bci);
		
		return sb.toString();
	}
}

enum Type {
	Reference,
	Global,
	String,
	Constant,
	Null
};