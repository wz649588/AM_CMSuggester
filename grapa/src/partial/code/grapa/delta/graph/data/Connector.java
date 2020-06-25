package partial.code.grapa.delta.graph.data;
public class Connector extends AbstractNode{
	public String type;
	
	public Connector(String type, String label, int side) {
		// TODO Auto-generated constructor stub
		this.type = type;
		this.label = label;
		this.side = side;
	}

	@Override
	public String toString() {
		// TODO Auto-generated method stub
		if(type.startsWith("com.ibm.wala.ipa.slicer.NormalStatement")){
			int mark = label.indexOf(" ");
			label = label.substring(mark+1);
			mark = label.indexOf(" ");
			if(mark>0){
				label = label.substring(0, mark);
			}
			return label;
		}else{			
			return type;
		}
	}
}
