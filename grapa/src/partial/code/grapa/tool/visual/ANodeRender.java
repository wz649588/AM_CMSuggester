package partial.code.grapa.tool.visual;

import java.awt.Component;
import java.awt.Dimension;
import java.awt.Rectangle;
import java.awt.geom.Point2D;

import edu.uci.ics.jung.algorithms.layout.Layout;
import edu.uci.ics.jung.graph.util.Context;
import edu.uci.ics.jung.visualization.Layer;
import edu.uci.ics.jung.visualization.RenderContext;
import edu.uci.ics.jung.visualization.renderers.VertexLabelAsShapeRenderer;
import edu.uci.ics.jung.visualization.renderers.VertexLabelRenderer;
import edu.uci.ics.jung.visualization.transform.shape.GraphicsDecorator;

public class ANodeRender extends VertexLabelAsShapeRenderer {

	

	@Override
	public void labelVertex(RenderContext rc, Layout layout, Object v,
			String label) {
		// TODO Auto-generated method stub
		edu.uci.ics.jung.graph.Graph graph = layout.getGraph();
        if(!rc.getVertexIncludePredicate().evaluate(Context.getInstance(graph, v)))
        {
            return;
        } else
        {
            GraphicsDecorator g = rc.getGraphicsContext();
            Component component = prepareRenderer(rc, rc.getVertexLabelRenderer(), label, rc.getPickedVertexState().isPicked(v), v);
            Dimension d = component.getPreferredSize();
            int h_offset = -d.width / 2;
            int v_offset = -d.height / 2;
            Point2D p = (Point2D)layout.transform(v);
            p = rc.getMultiLayerTransformer().transform(Layer.LAYOUT, p);
            int x = (int)p.getX();
            int y = (int)p.getY();
            g.draw(component, rc.getRendererPane(), x + h_offset, y + v_offset, d.width, d.height, true);
            Dimension size = component.getPreferredSize();
            Rectangle bounds = new Rectangle(-size.width / 2 - 2, -size.height / 2 - 2, (size.width + 4)/4, size.height);
            shapes.put(v, bounds);
            return;
        }
	}

	public ANodeRender(RenderContext rc) {
		super(rc);
		// TODO Auto-generated constructor stub
	}

}
