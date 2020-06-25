package ch.uzh.ifi.seal.changedistiller.ast.java;

/**
 * 
 * @author Ye Wang
 * @since 02/12/2018
 *
 */
public class WhiteSpaceUtil {
	
	public static String removeWhiteSpaces(String s) {
		return s.replace(" ", "");
	}
	
	public static void main(String[] args) {
		String s = "org.apache.cassandra.service.StorageProxy.counterWriteTask(IMutation,Multimap<InetAddress, InetAddress>,IWriteResponseHandler,String,ConsistencyLevel)";
		String ss = removeWhiteSpaces(s);
		System.out.println(ss);
	}

}
