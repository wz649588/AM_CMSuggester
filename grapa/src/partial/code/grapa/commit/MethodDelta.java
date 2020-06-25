package partial.code.grapa.commit;

import edu.uci.ics.jung.graph.DirectedSparseGraph;
import partial.code.grapa.dependency.graph.StatementEdge;
import partial.code.grapa.dependency.graph.StatementNode;
import partial.code.grapa.mapping.ClientMethod;

public class MethodDelta {	
	public String oldKey;
	public String oldName;
	public String oldSig;
	public String newKey;
	public String newName;
	public String newSig;
	public DirectedSparseGraph<StatementNode, StatementEdge> deltaGraph;
	
	public MethodDelta(ClientMethod oldMethod, ClientMethod newMethod,
			DirectedSparseGraph<StatementNode, StatementEdge> dg) {
		// TODO Auto-generated constructor stub
		oldKey = oldMethod.key;
		oldName = oldMethod.methodName;
		oldSig = oldMethod.sig;
		newKey = newMethod.key;
		newName = newMethod.methodName;
		newSig = newMethod.sig;
		deltaGraph = dg;
		
	}
}
