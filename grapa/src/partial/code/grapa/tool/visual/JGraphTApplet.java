package partial.code.grapa.tool.visual;

import java.awt.BasicStroke;
import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.LayoutManager;
import java.awt.Paint;
import java.awt.geom.Rectangle2D;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.swing.JApplet;



import javax.swing.JComboBox;
import javax.swing.JRootPane;

import org.apache.commons.collections15.Transformer;
import org.apache.commons.collections15.functors.ConstantTransformer;


import edu.uci.ics.jung.algorithms.layout.FRLayout2;
import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.uci.ics.jung.graph.ObservableGraph;
import edu.uci.ics.jung.visualization.VisualizationViewer;
import edu.uci.ics.jung.visualization.control.DefaultModalGraphMouse;
import edu.uci.ics.jung.visualization.decorators.ToStringLabeller;
import edu.uci.ics.jung.visualization.renderers.DefaultEdgeLabelRenderer;
import edu.uci.ics.jung.visualization.renderers.DefaultVertexLabelRenderer;
import edu.uci.ics.jung.visualization.renderers.GradientVertexRenderer;
import edu.uci.ics.jung.visualization.renderers.Renderer;
import edu.uci.ics.jung.visualization.renderers.VertexLabelAsShapeRenderer;

public class JGraphTApplet extends JApplet{
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private static final Color DEFAULT_BG_COLOR = Color.decode("#FAFBFF");
	private static final Dimension DEFAULT_SIZE = new Dimension(530, 320);
	private FRLayout2 layout;
	private VisualizationViewer vv;
	private ObservableGraph og;
	
	public void init(DirectedSparseGraph g) {
		// TODO Auto-generated method stub
		og = new ObservableGraph(g);
		resize(DEFAULT_SIZE);    
	    layout = new FRLayout2(og);
        vv = new VisualizationViewer(layout, new Dimension(600, 600));
        JRootPane rp = getRootPane();
        rp.putClientProperty("defeatSystemEventQueueCheck", Boolean.TRUE);
        getContentPane().setLayout(new FlowLayout());
        getContentPane().setBackground(Color.lightGray);
        getContentPane().setFont(new Font("Serif", 0, 12));
        vv.getModel().getRelaxer().setSleepTime(500L);
        
        ANodeRender vlasr = new ANodeRender(vv.getRenderContext());
        vv.getRenderContext().setVertexShapeTransformer(vlasr);
        vv.getRenderer().setVertexLabelRenderer(vlasr);
        vv.getRenderContext().setVertexLabelRenderer(new DefaultVertexLabelRenderer(Color.red));
        vv.getRenderContext().setVertexLabelTransformer(new ToStringLabeller());
        vv.getRenderer().setVertexRenderer(new GradientVertexRenderer(Color.gray, Color.gray, true));
        
        
//      vv.getRenderer().getVertexLabelRenderer().setPosition(edu.uci.ics.jung.visualization.renderers.Renderer.VertexLabel.Position.CNTR);
        
        vv.getRenderContext().setEdgeDrawPaintTransformer(new ConstantTransformer(Color.black));
        vv.getRenderContext().setEdgeStrokeTransformer(new ConstantTransformer(new BasicStroke(2.5F)));
        vv.getRenderContext().setEdgeLabelRenderer(new MyDefaultEdgeLaberRenderer(Color.black, Color.black));
        vv.getRenderContext().setEdgeLabelTransformer(new ToStringLabeller());
 
         
        vv.setForeground(Color.white);
        
        DefaultModalGraphMouse graphMouse = new DefaultModalGraphMouse();
        vv.setGraphMouse(graphMouse);
        JComboBox modeBox = graphMouse.getModeComboBox();
        modeBox.addItemListener(((DefaultModalGraphMouse)vv.getGraphMouse()).getModeListener());
        vv.add(modeBox);
        getContentPane().add(vv);
	}

	
	

   
}
