package partial.code.grapa.delta.graph;

public class UpdateNode extends AbstractNodeEdit {
	private String to;
	public UpdateNode(String from, String to) {
		super(from);
		this.to = to;
		// TODO Auto-generated constructor stub
	}
	@Override
	public String toString() {
		// TODO Auto-generated method stub
		return "UpdateNode:"+super.toString()+"=>"+to;
	}
}
