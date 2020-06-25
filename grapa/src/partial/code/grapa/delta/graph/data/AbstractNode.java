package partial.code.grapa.delta.graph.data;

public abstract class AbstractNode {
	public static final int LEFT  = 1;
	public static final int RIGHT = 2;
	public int side;
	public String label;
	public String label2;
	@Override
	public String toString() {
		// TODO Auto-generated method stub
		return label;
	}		
}
