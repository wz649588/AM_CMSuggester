package edu.vt.cs.extraction;

import static java.nio.file.StandardOpenOption.*;

import java.io.IOException;
import java.nio.file.DirectoryIteratorException;
import java.nio.file.DirectoryStream;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;

import org.jgrapht.Graph;

import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.vt.cs.graph.ReferenceEdge;
import edu.vt.cs.graph.ReferenceNode;

/**
 * This class just generates the statistics of attribute
 * of vertices and edges of graphs
 * @author Ye Wang
 * @since 12/13/2016
 */
public class GraphResultStat {

	public static void main(String[] args) throws IOException {
		String inputDir = "/Users/Vito/Documents/VT/2016fall/SE/grapa_results/derby";
//		String inputDir = "/Users/Vito/Documents/VT/2016fall/SE/grapa_results/1";
		String vertexStat = "/Users/Vito/Documents/VT/2016fall/SE/vertexStat.csv";
		String edgeStat = "/Users/Vito/Documents/VT/2016fall/SE/edgeStat.csv";
		
		// write the first line of output vertex statistics file
		Path vertexStatPath = FileSystems.getDefault().getPath(vertexStat);
		 String vertexStatHeader = "type\n";
//		String vertexStatHeader = "";
		
		// write the first line of output edge statistics file
		Path edgeStatPath = FileSystems.getDefault().getPath(edgeStat);
		String edgeStatHeader = "type,dep,t<-C-(1),t-C->(2),t<-D-(4),t-D->(8)\n";
		
		StringBuilder vertexBuilder = new StringBuilder();
		vertexBuilder.append(vertexStatHeader);
		
		StringBuilder edgeBuilder = new StringBuilder();
		edgeBuilder.append(edgeStatHeader);
		
		// read the XML files to generate JUNG objects
		Path path = FileSystems.getDefault().getPath(inputDir);
		try {
			DirectoryStream<Path> stream = Files.newDirectoryStream(path);
			int pathCounter = 0;
			for (Path subpath: stream) {
				System.out.println(++pathCounter);
				if (Files.isDirectory(subpath)) {
					DirectoryStream<Path> substream = Files.newDirectoryStream(subpath, "impact_*.xml");
					for (Path filePath: substream) {
						DirectedSparseGraph<ReferenceNode, ReferenceEdge> jung = 
								PatternExtractor.readXMLFile(filePath);
						Graph<ReferenceNode, ReferenceEdge> g =
								PatternExtractor.convertJungToJGraphT(jung);
						for (ReferenceNode vertex: g.vertexSet()) {
							String vertexType = PatternDotUtil.resolveNodeType(vertex.type);
							vertexBuilder.append(vertexType).append("\n");
						}
						for (ReferenceEdge edge: g.edgeSet()) {
							String edgeType;
							switch (edge.type) {
								case ReferenceEdge.FIELD_ACCESS:
									edgeType = "FIELD_ACCESS";
									break;
								case ReferenceEdge.METHOD_INVOKE:
									edgeType = "METHOD_INVOKE";
									break;
								case ReferenceEdge.METHOD_OVERRIDE:
									edgeType = "METHOD_OVERRIDE";
									break;
								default:
									edgeType = "";
							}
							edgeBuilder.append(edgeType).append(",")
								.append(edge.dep).append(",");
							if ((edge.dep & ReferenceEdge.CALLEE_CONTROL_DEP_OTHER) == ReferenceEdge.CALLEE_CONTROL_DEP_OTHER)
								edgeBuilder.append("1,");
							else
								edgeBuilder.append("0,");
							if ((edge.dep & ReferenceEdge.OTHER_CONTROL_DEP_CALLEE) == ReferenceEdge.OTHER_CONTROL_DEP_CALLEE)
								edgeBuilder.append("1,");
							else
								edgeBuilder.append("0,");
							if ((edge.dep & ReferenceEdge.CALLEE_DATA_DEP_OTHER) == ReferenceEdge.CALLEE_DATA_DEP_OTHER)
								edgeBuilder.append("1,");
							else
								edgeBuilder.append("0,");
							if ((edge.dep & ReferenceEdge.OTHER_DATA_DEP_CALLEE) == ReferenceEdge.OTHER_DATA_DEP_CALLEE)
								edgeBuilder.append("1\n");
							else
								edgeBuilder.append("0\n");
						}
					}
				}
			}
		} catch (IOException | DirectoryIteratorException e) {
			System.err.println(e);
		}
		
		Files.write(vertexStatPath, vertexBuilder.toString().getBytes(), CREATE, TRUNCATE_EXISTING);
		Files.write(edgeStatPath, edgeBuilder.toString().getBytes(), CREATE, TRUNCATE_EXISTING);
		
	}

}
