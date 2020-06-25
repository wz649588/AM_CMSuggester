package partial.code.grapa.dependency.graph;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;

import partial.code.grapa.delta.graph.GraphComparator;

import com.ibm.wala.ipa.slicer.NormalStatement;
import com.ibm.wala.ipa.slicer.Statement;
import com.ibm.wala.ssa.IR;

public class StatementNode {
	public int side = 0;
	public Statement statement;	
	public List<Statement> statements; //added by nameng to allow m-to-1 mappings between statements and statementNodes
	public List<ASTNode> nodes; //modified by nameng, since sometimes it is really difficult to split between statements in the same line
	public static final int LEFT  = 1;
	public static final int RIGHT = 2;
	
	public StatementNode(Statement statement) {
		// TODO Auto-generated constructor stub
		this.statement = statement;
		this.statements = new ArrayList<Statement>();
	}
	
	public void addStatement(Statement statement) {
		statements.add(statement);
	}

	@Override
	public String toString() {
		if (nodes != null) {
			StringBuffer buf = new StringBuffer(statement.toString() + "\n");
			for (ASTNode n : nodes) {
				buf.append(n).append("\n");
			}
			return buf.toString();
		} else
			return statement.toString();
	}

	public boolean isSameType(StatementNode sn) {
		// TODO Auto-generated method stub
		String t1;
		String t2;
		if(statement instanceof NormalStatement&&sn.statement instanceof NormalStatement){
			NormalStatement ns1 = (NormalStatement)statement;
			NormalStatement ns2 = (NormalStatement)sn.statement;
			t1 = ns1.getInstruction().getClass().getName();//modified by Na Meng
			t2 = ns2.getInstruction().getClass().getName();
		}else{
			t1 = statement.getClass().getName(); // modified by Na Meng
			t2 = sn.statement.getClass().getName();
		}
		return t1.compareTo(t2)==0;
	}

	public boolean isSameInterestingType(StatementNode sn, IR ir) {
		// TODO Auto-generated method stub
		return isSameType(sn)&&isInterestingType(ir);
	}

	private boolean isInterestingType(IR ir) {
		// TODO Auto-generated method stub
		boolean bInte = false;
		if(statement instanceof NormalStatement){
			String type = GraphComparator.getComparedLabel(ir, statement);
			if(type.startsWith("invoke")){
				bInte = true;
			}else if(type.startsWith("put")){
				bInte = true;
			}else if(type.startsWith("get")){
				bInte = true;
			}
		}
		return bInte;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((statement == null) ? 0 : statement.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		StatementNode other = (StatementNode) obj;
		if (statement == null) {
			if (other.statement != null)
				return false;
		} else if (!statement.equals(other.statement))
			return false;
		return true;
	}

}
