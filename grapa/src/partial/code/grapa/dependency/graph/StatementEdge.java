package partial.code.grapa.dependency.graph;

public class StatementEdge {
	public int type;
	public StatementNode from;
	public StatementNode to;
	public static final int DATA_FLOW = 0;
	public static final int CONTROL_FLOW = 1;
	public static final int CHANGE = 2;

	public StatementEdge(StatementNode from, StatementNode to, int m) {
		// TODO Auto-generated constructor stub
		this.from = from;
		this.to = to;
		type = m;
	}

	@Override
	public String toString() {
		// TODO Auto-generated method stub
		String line = "";
		if(type == DATA_FLOW){
			line = "df";
		}else if(type == CONTROL_FLOW){
			line = "cf";
		}else if(type == CHANGE){
			line = "m";
		}
		return line;
	}

}
