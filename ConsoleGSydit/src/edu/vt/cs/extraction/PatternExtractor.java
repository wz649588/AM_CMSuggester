package edu.vt.cs.extraction;

import static java.nio.file.StandardOpenOption.*;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.DirectoryIteratorException;
import java.nio.file.DirectoryStream;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Scanner;
import java.util.Set;

import com.thoughtworks.xstream.XStream;
import com.thoughtworks.xstream.io.xml.StaxDriver;

import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.vt.cs.graph.ReferenceNode;
import edu.vt.cs.graph.ReferenceEdge;

import org.jgrapht.Graph;
import org.jgrapht.GraphMapping;
import org.jgrapht.graph.DefaultDirectedGraph;
import org.jgrapht.alg.isomorphism.VF2GraphIsomorphismInspector;
import org.jgrapht.alg.isomorphism.VF2SubgraphIsomorphismInspector;

/**
 * Extract common patterns among graphs.
 * The data in the input directory are serialized JUNG objects.
 * The data in the output directory are serialized JGraphT objects.
 * The statistics of outputs are stored in a CSV file.
 * The unique common patterns are stored in a separate directory, 
 * in which the statistics of the common patterns are stored.
 * 
 * @author Ye Wang
 * @since 10/23/2016
 */
public class PatternExtractor {
	
	// input directory
	private final String inputDir;
	
	// output directory
	private final String outputDir;
	
	// location of result log
	// content format:
	// bug1,bug2,subg1,subg2,mapping,vertex_num,edge_num
	private final String resultLog;
	
	// unsupervised pattern structure set directory
	private final String patternSetDir;
	
	private final VertexComparator vertexComparator;
	
	private final EdgeComparator edgeComparator;
	
	public PatternExtractor(String inputDir, String outputDir, String resultLog, String patternSetDir) {
		this.inputDir = inputDir;
		this.outputDir = outputDir;
		this.resultLog = resultLog;
		this.patternSetDir = patternSetDir;
		this.vertexComparator = new VertexComparator();
		this.edgeComparator = new EdgeComparator();
	}
	
	public static void main(String[] args) throws IOException {
		String dirname = "/Users/Vito/Documents/VT/2016fall/SE/grapa_results_inuse/derby";
		String isoDir = "/Users/Vito/Documents/VT/2016fall/SE/iso_subgraph";
		String resultLog = "/Users/Vito/Documents/VT/2016fall/SE/mapping_table.csv";
		String patternSetDir = "/Users/Vito/Documents/VT/2016fall/SE/pattern_set";
		
//		String dirname = "/Users/Vito/Documents/VT/2016fall/SE/grapa_results_temp_inuse/derby";
//		String isoDir = "/Users/Vito/Documents/VT/2016fall/SE/iso_subgraph_temp";
//		String resultLog = "/Users/Vito/Documents/VT/2016fall/SE/mapping_table_temp.csv";
		
		// create the directory of the pattern set
		Path patternSetPath = FileSystems.getDefault().getPath(patternSetDir);
		Files.createDirectories(patternSetPath);
		
		// check if the patternInfo.csv file exists
		Path patternInfoPath = FileSystems.getDefault().getPath(patternSetDir, "patternInfo.csv");
		if (Files.notExists(patternInfoPath)) {
			// create the table head of the patternInfo file
			String thisPatternInfo = String.format("pattern_code,vertex_num,edge_num\n");
			Files.write(patternInfoPath, thisPatternInfo.getBytes(), CREATE);
		}
		
		PatternExtractor extractor = new PatternExtractor(dirname, isoDir, resultLog, patternSetDir);
		
		FileWriter fileWriter = new FileWriter(resultLog, false);
		fileWriter.write("bug1,bug2,subg1,subg2,mapping,vertex_num,edge_num,pattern_code\n");
		fileWriter.close();
		
		// find bug output directories and the XML files in them
		List<BugGraphPaths> graphPaths = extractor.findBugGraphPaths();
		
		for (int i = 0; i < graphPaths.size(); i++) {
			for (int j = i + 1; j < graphPaths.size(); j++) {
				BugGraphPaths p1 = graphPaths.get(i);
				BugGraphPaths p2 = graphPaths.get(j);
				// find isomorphic subgraphs, and write them to files 
				extractor.findIsoSubgraphs(p1, p2);
			}
		}
		
	}
	
	/**
	 * read JGraphT object from XML file
	 * @param filePath the file Path object of XML file
	 * @return JGraphT object
	 */
	@SuppressWarnings("unchecked")
	public static Graph<ReferenceNode, ReferenceEdge> readJgraphtFromXml(Path filePath) {
		XStream xstream = new XStream(new StaxDriver());
		File xmlFile = filePath.toFile();
		return (Graph<ReferenceNode, ReferenceEdge>)xstream.fromXML(xmlFile);
	}
	
	/**
	 * read xml file to build JUNG graph
	 * @param filePath the file Path object of XML file
	 * @return JUNG graph
	 */
	@SuppressWarnings("unchecked")
	public static DirectedSparseGraph<ReferenceNode, ReferenceEdge> readXMLFile(Path filePath) {
		XStream xstream = new XStream(new StaxDriver());
		File xmlFile = filePath.toFile();
		return (DirectedSparseGraph<ReferenceNode, ReferenceEdge>)xstream.fromXML(xmlFile);
	}
	
	/**
	 * Convert JUNG to JGraphT
	 * @param g JUNG graph
	 * @return JGraphT graph
	 */
	public static Graph<ReferenceNode, ReferenceEdge>
			convertJungToJGraphT(DirectedSparseGraph<ReferenceNode, ReferenceEdge> graph) {
		Graph<ReferenceNode, ReferenceEdge> g =
				new DefaultDirectedGraph<ReferenceNode, ReferenceEdge>(ReferenceEdge.class);
		
		Collection<ReferenceNode> vertices = graph.getVertices();
		for (ReferenceNode vertex: vertices) {
			g.addVertex(vertex);
		}
		
		Collection<ReferenceEdge> edges = graph.getEdges();
		for (ReferenceEdge edge: edges) {
			ReferenceNode sourceVertex = edge.from;
			ReferenceNode targetVertex = edge.to;
			try {
				g.addEdge(sourceVertex, targetVertex, edge);
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		return g;
	}
	
	/**
	 * find bug output directories and the XML files in them
	 * @param dir top directory
	 * @return bug output directories and XML files in them
	 */
	public List<BugGraphPaths> findBugGraphPaths() {
		List<BugGraphPaths> bugOutputs = new ArrayList<BugGraphPaths>();
		Path path = FileSystems.getDefault().getPath(inputDir);
		try {
			DirectoryStream<Path> stream = Files.newDirectoryStream(path);
			Set<String> bugNums = new HashSet<String>();
			for (Path subpath: stream) {
				if (Files.isDirectory(subpath)) {
					DirectoryStream<Path> substream = Files.newDirectoryStream(subpath, "impact_*.xml");
					String bugName = subpath.getFileName().toString();
					String bugNum = parseBugNum(bugName);
					if (!bugNums.contains(bugNum)) {
						bugNums.add(bugNum);
						List<Path> xmlPaths = new ArrayList<Path>();
						for (Path filepath: substream) {
							xmlPaths.add(filepath);
						}
						if (!xmlPaths.isEmpty()) {
							bugOutputs.add(new BugGraphPaths(bugName, xmlPaths));
						}
					}
				}
		    }
		} catch (IOException | DirectoryIteratorException e) {
			System.err.println(e);
		}
		return bugOutputs;
	}
	
	/**
	 * This method aids the method findBugGraphPaths() to find
	 * the bug number in the end of a bug name.
	 * E.g., for 123456_DERBY-7890, it returns 7890.
	 * For 987654_DERBY-32_found, it returns 32.
	 * @param bugName full bug name
	 * @return bug number in the end of bug name
	 */
	private String parseBugNum(String bugName) {
		int dashPos = bugName.indexOf('-');
		int begin = dashPos + 1;
		int end = begin;
		while(end < bugName.length() && Character.isDigit(bugName.charAt(end)))
			end++;
		return bugName.substring(begin, end);
	}
	
	/**
	 * find the isomorphic subgraphs, and write them to files
	 * @param graphPaths1 first 
	 * @param graphPaths2 second
	 * @param dir output result directory
	 * @throws IOException 
	 */
	public void findIsoSubgraphs(BugGraphPaths graphPaths1, BugGraphPaths graphPaths2) throws IOException {
		XStream xstream = new XStream(new StaxDriver());
		String resultDir = outputDir + "/" + graphPaths1.name + "/" + graphPaths2.name;
		Path resultPath = FileSystems.getDefault().getPath(resultDir);
		for (Path path1: graphPaths1.xmlPaths) {
			for (Path path2: graphPaths2.xmlPaths) {
				DirectedSparseGraph<ReferenceNode, ReferenceEdge> jungGraph1 = readXMLFile(path1);
				DirectedSparseGraph<ReferenceNode, ReferenceEdge> jungGraph2 = readXMLFile(path2);
				
				Graph<ReferenceNode, ReferenceEdge> g1 = convertJungToJGraphT(jungGraph1);
				Graph<ReferenceNode, ReferenceEdge> g2 = convertJungToJGraphT(jungGraph2);
				
				// Analyze isomorphic subgraphs and get mappings
				VF2SubgraphIsomorphismInspector<ReferenceNode, ReferenceEdge> isoInspector =
						new VF2SubgraphIsomorphismInspector<ReferenceNode, ReferenceEdge>(g1, g2, vertexComparator, edgeComparator);
				Iterator<GraphMapping<ReferenceNode, ReferenceEdge>> isoIterator = isoInspector.getMappings();
				
				// get file names without extensions
				// e.g. get "impact_1" from "impact_1.xml";
				String filename1 = path1.getFileName().toString().replaceFirst("[.][^.]+$", "");
				String filename2 = path2.getFileName().toString().replaceFirst("[.][^.]+$", "");
				String filenamePrefix = resultDir + "/" + filename1 + "_" + filename2 + "_";
				
				//**************DEBUG*******************
//				PatternDotUtil.dotify(g1, resultDir + "/" + graphPaths1.name + "_" + filename1 + ".pdf");
//				PatternDotUtil.dotify(g2, resultDir + "/" + graphPaths2.name + "_" + filename2 + ".pdf");
				//**************DEBUG*******************
				
				// create output directories
				if (isoIterator.hasNext()) {
					try {
						Files.createDirectories(resultPath);
					} catch (IOException e) {
						e.printStackTrace();
						System.exit(-1);
					}
				}
				
				// result set
				List<Graph<ReferenceNode, ReferenceEdge>> subgraphListA = new ArrayList<Graph<ReferenceNode, ReferenceEdge>>();
				List<Graph<ReferenceNode, ReferenceEdge>> subgraphListB = new ArrayList<Graph<ReferenceNode, ReferenceEdge>>();
				
				
				int mappingNum = 0;
				while (isoIterator.hasNext()) {
					GraphMapping<ReferenceNode, ReferenceEdge> mapping = isoIterator.next();
					
					
					
					
					// find subgraphs through mappings, and export subgraphs
					Graph<ReferenceNode, ReferenceEdge> subgraph1 =
							new DefaultDirectedGraph<ReferenceNode, ReferenceEdge>(ReferenceEdge.class);
					Graph<ReferenceNode, ReferenceEdge> subgraph2 =
							new DefaultDirectedGraph<ReferenceNode, ReferenceEdge>(ReferenceEdge.class);
					for (ReferenceNode vertexInG1: g1.vertexSet()) {
						ReferenceNode vertexInG2 = mapping.getVertexCorrespondence(vertexInG1, true);
						if (vertexInG2 != null) {
							subgraph1.addVertex(vertexInG1);
							subgraph2.addVertex(vertexInG2);
						}
					}
					for (ReferenceEdge edgeInG1: g1.edgeSet()) {
						ReferenceEdge edgeInG2 = mapping.getEdgeCorrespondence(edgeInG1, true);
						if (edgeInG2 != null) {
							subgraph1.addEdge(edgeInG1.from, edgeInG1.to, edgeInG1);
							subgraph2.addEdge(edgeInG2.from, edgeInG2.to, edgeInG2);
						}
					}
					
					// check if the subgraph has already existed in result set
					boolean combinationExist = checkExistence(subgraph1, subgraph2, subgraphListA, subgraphListB);
					
					if (!combinationExist) {
						// export subgraphs
						String pdfPath1 = filenamePrefix + mappingNum + "_l.pdf";
						PatternDotUtil.dotify(subgraph1, pdfPath1);
						String pdfPath2 = filenamePrefix + mappingNum + "_r.pdf";
						PatternDotUtil.dotify(subgraph2, pdfPath2);
						
						// check if the structure of the subgraph exists in the pattern set
						String patternCode = retrievePatternCode(subgraph1);
						if (patternCode == null) { // new pattern
							// get the last number of the pattern code
							int lastNumber = 0;
							File lastNumberFile = new File(this.patternSetDir + "/lastNumber.txt");
							if (lastNumberFile.exists()) {
								Scanner lastNumberScanner = new Scanner(lastNumberFile);
								lastNumber = lastNumberScanner.nextInt();
								lastNumberScanner.close();
							}
							
							
							// get the current number for pattern code
							int currentNumber = lastNumber + 1;
							
							// save the graph object in XML file
							Path xmlPath = FileSystems.getDefault().getPath(this.patternSetDir + "/" + currentNumber + ".xml");
							try (BufferedOutputStream outputStream = new BufferedOutputStream(
									Files.newOutputStream(xmlPath, CREATE, TRUNCATE_EXISTING))) {
								xstream.toXML(subgraph1, outputStream);
							} catch (IOException x) {
							      x.printStackTrace();
							      System.exit(-1);
						    }
							
							// rewrite the last number file
							Path lastNumberPath = FileSystems.getDefault().getPath(this.patternSetDir + "/lastNumber.txt");
							byte[] buf = String.valueOf(currentNumber).getBytes();
							Files.write(lastNumberPath, buf, WRITE, CREATE, TRUNCATE_EXISTING);
							
							// convert the graph to PDF file
							PatternDotUtil.dotify(subgraph1, this.patternSetDir + "/" + currentNumber + ".pdf");
							
							// append the information for the pattern
							Path patternInfoPath = FileSystems.getDefault().getPath(this.patternSetDir, "patternInfo.csv");
							// format: pattern_code,vertex_num,edge_num
							String thisPatternInfo = String.format("%d,%d,%d%n", currentNumber,
									subgraph1.vertexSet().size(), subgraph1.edgeSet().size());
							Files.write(patternInfoPath, thisPatternInfo.getBytes(), APPEND);
							
							patternCode = String.valueOf(currentNumber);
						}
						
						// write the number of vertices and the number of edges to file
						FileWriter fileWriter = new FileWriter(this.resultLog, true);
						String row = String.format("%s,%s,%s,%s,%d,%d,%d,%s%n", graphPaths1.name,
								graphPaths2.name, filename1, filename2, mappingNum,
								subgraph1.vertexSet().size(), subgraph1.edgeSet().size(),
								patternCode);
						fileWriter.write(row);
						fileWriter.close();
						
						System.out.print(row);
						
						// Add graphs to result lists
						subgraphListA.add(subgraph1);
						subgraphListB.add(subgraph2);
						
						// Save subgraph objects to files
						Path xmlPath1 = FileSystems.getDefault().getPath(filenamePrefix + mappingNum + "_l.xml");
						try (BufferedOutputStream outputStream = new BufferedOutputStream(
								Files.newOutputStream(xmlPath1, CREATE, TRUNCATE_EXISTING))) {
							xstream.toXML(subgraph1, outputStream);
						} catch (IOException x) {
						      x.printStackTrace();
						      System.exit(-1);
					    }
						Path xmlPath2 = FileSystems.getDefault().getPath(filenamePrefix + mappingNum + "_r.xml");
						try (BufferedOutputStream outputStream = new BufferedOutputStream(
								Files.newOutputStream(xmlPath2, CREATE, TRUNCATE_EXISTING))) {
							xstream.toXML(subgraph2, outputStream);
						} catch (IOException x) {
						      x.printStackTrace();
						      System.exit(-1);
					    }
						
						mappingNum++;
					}
					
				} // while
				
			} // for
		} // for
	}
	
	/**
	 * get the pattern code from the pattern set
	 * @param graph the graph of the pattern structure
	 * @return pattern code if the pattern exists and otherwise null
	 */
	private String retrievePatternCode(
			Graph<ReferenceNode, ReferenceEdge> graph) {
		// read the XMLs
		Path patternSetPath = FileSystems.getDefault().getPath(this.patternSetDir);
		try (DirectoryStream<Path> stream = Files.newDirectoryStream(patternSetPath, "*.xml")) {
			for (Path file: stream) {
				// read the Graph object from the XML file
				XStream xstream = new XStream(new StaxDriver());
				File xmlFile = file.toFile();
				@SuppressWarnings("unchecked")
				Graph<ReferenceNode, ReferenceEdge> g = (Graph<ReferenceNode, ReferenceEdge>)xstream.fromXML(xmlFile);
				
		        // check if the given graph and the graph in the set
				// are of the same structure.
				if (isStructureSame(graph, g)) {
					// get the pattern code
					String fullFileName = file.getFileName().toString();
					String patternCode = fullFileName.substring(0, fullFileName.length() - 4);
					return patternCode;
				}
				
		    }
		} catch (IOException | DirectoryIteratorException x) {
		    // IOException can never be thrown by the iteration.
		    // In this snippet, it can only be thrown by newDirectoryStream.
		    System.err.println(x);
		}
		
		return null;
	}
	
	
	private boolean isStructureSame(Graph<ReferenceNode, ReferenceEdge> g1,
			Graph<ReferenceNode, ReferenceEdge> g2) {
//		Comparator<ReferenceNode> vertexComparator = new Comparator<ReferenceNode>() {
//			public int compare(ReferenceNode n1, ReferenceNode n2) {
//				return n1.type - n2.type;
//			}
//		};
//		Comparator<ReferenceEdge> edgeComparator = new Comparator<ReferenceEdge>() {
//			public int compare(ReferenceEdge e1, ReferenceEdge e2) {
//				return e1.type - e2.type;
//			}
//		};
		VF2GraphIsomorphismInspector<ReferenceNode,ReferenceEdge> isoInspector =
				new VF2GraphIsomorphismInspector<>(g1, g2, vertexComparator, edgeComparator);
		return isoInspector.isomorphismExists();
	}
	
	private void saveGraphInXml(Graph<ReferenceNode, ReferenceEdge> graph, String xml) {
		XStream xstream = new XStream(new StaxDriver());
		Path xmlPath = FileSystems.getDefault().getPath(xml);
		try (BufferedOutputStream outputStream = new BufferedOutputStream(
				Files.newOutputStream(xmlPath, CREATE, TRUNCATE_EXISTING))) {
			xstream.toXML(graph, outputStream);
		} catch (IOException x) {
		      x.printStackTrace();
		      System.exit(-1);
	    }
	}

	// check if the subgraph pair g1 and g2 exists in list1 and list2
	private boolean checkExistence(Graph<ReferenceNode, ReferenceEdge> g1, Graph<ReferenceNode, ReferenceEdge> g2,
			List<Graph<ReferenceNode, ReferenceEdge>> list1, List<Graph<ReferenceNode, ReferenceEdge>> list2) {
		Graph<ReferenceNode, ReferenceEdge> graphInList1, graphInList2;
		for (int i = 0; i < list1.size(); i++) {
			graphInList1 = list1.get(i);
			graphInList2 = list2.get(i);
			if (contain(g1, graphInList1) && contain(g2, graphInList2)) 
				return true;	
		}
		return false;
	}
	
	// used by method checkExistence
	private boolean contain(Graph<ReferenceNode, ReferenceEdge> child, Graph<ReferenceNode, ReferenceEdge> parent) {
		for (ReferenceNode n: child.vertexSet()) {
			if (!parent.containsVertex(n)) {
				return false;
			}
		}
		for (ReferenceEdge e: child.edgeSet()) {
			if (!parent.containsEdge(e)) {
				return false;
			}
		}
		return true;
	}
}
