package partial.code.grapa.tool.visual;

import java.awt.FlowLayout;
import java.awt.LayoutManager;

import javax.swing.JApplet;
import javax.swing.JFrame;



import edu.uci.ics.jung.graph.DirectedSparseGraph;

public class JGraphTViewer{

	public void show(DirectedSparseGraph g, String title) {
		// TODO Auto-generated method stub
		JGraphTApplet applet = new JGraphTApplet();
		applet.init(g);
		JFrame frame = new JFrame();
	    frame.getContentPane().add(applet);
        frame.setTitle(title);
        frame.setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
        frame.pack();
        frame.setVisible(true);
	}

}
