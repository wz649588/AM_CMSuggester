package partial.code.grapa.commit;

public class DeltaInfo {
	public int deltaFile = 0;
	public int modifiedFile = 0;
	public int deltaMethod = 0;
	public int modifiedMethod = 0;
	public int deltaGraphNode = 0;
	
	public void println() {
		// TODO Auto-generated method stub
		System.out.println("deltaFile:"+deltaFile+" modifiedFile:"+modifiedFile+" deltaMethod:"+deltaMethod
				+" modifiedMethod:"+modifiedMethod+" deltaGraphNode:"+deltaGraphNode);
	}
}
