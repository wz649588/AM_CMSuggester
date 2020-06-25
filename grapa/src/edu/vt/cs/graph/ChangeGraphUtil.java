package edu.vt.cs.graph;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Iterator;

import partial.code.grapa.delta.graph.data.AbstractNode;
import partial.code.grapa.delta.graph.data.Edge;

import com.ibm.wala.examples.drivers.PDFTypeHierarchy;
import com.thoughtworks.xstream.XStream;
import com.thoughtworks.xstream.io.xml.StaxDriver;

import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.vt.cs.graph.GraphUtil2;

public class ChangeGraphUtil {

	public static void writeRelationGraph(DirectedSparseGraph<ReferenceNode, ReferenceEdge> g, String filename) {
		String xmlFile = filename + ".xml";
		xmlFile = xmlFile.replaceAll("<", "");
		xmlFile = xmlFile.replaceAll(">", "");
		XStream xstream = new XStream(new StaxDriver());
		try{
			 File file = new File(xmlFile);
			 FileWriter writer=new FileWriter(file);
			 String content = xstream.toXML(g);
			 writer.write(content);
			 writer.close();
		} catch (IOException e){
			 e.printStackTrace();
		}
		 
		String psFile =  filename + ".pdf";
		psFile = psFile.replaceAll("<", "");
		psFile = psFile.replaceAll(">", "");		
		
		ChangeGraphDotUtil.dotify(g, PDFTypeHierarchy.DOT_FILE, psFile, GraphUtil2.dotExe);
	}
}
