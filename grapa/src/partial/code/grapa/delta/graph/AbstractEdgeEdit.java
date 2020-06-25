package partial.code.grapa.delta.graph;

abstract public class AbstractEdgeEdit extends AbstractEdit{
	private String from;
	private String to;
	private int type;
	
	public AbstractEdgeEdit(String f, String t, int type) {
		// TODO Auto-generated constructor stub
		from = f;
		to = t;
		this.type = type;
	}
	
	public String getFrom() {
		return from;
	}

	public String getTo() {
		return to;
	}

	public int getType() {
		return type;
	}

	@Override
	public String toString() {
		// TODO Auto-generated method stub
		return from+"-"+type+"->"+to;
	}
}
