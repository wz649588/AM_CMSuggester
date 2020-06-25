package partial.code.grapa.tool.visual;

import java.awt.Color;
import java.awt.Component;
import java.awt.Font;

import javax.swing.JComponent;

import edu.uci.ics.jung.visualization.renderers.DefaultVertexLabelRenderer;

public class MyDefaultVertexLaberRenderer extends DefaultVertexLabelRenderer
{
    protected Color unpickedVertexLabelColor = Color.BLACK;

    public MyDefaultVertexLaberRenderer(Color unpickedVertexLabelColor, Color pickedVertexLabelColor)
    {
        super(pickedVertexLabelColor);
        this.unpickedVertexLabelColor = unpickedVertexLabelColor;
    }

    public <V> Component getVertexLabelRendererComponent(JComponent vv, Object value, Font font, boolean isSelected, V vertex)
    {
        super.setForeground(unpickedVertexLabelColor);
        if (isSelected) setForeground(pickedVertexLabelColor);
        super.setBackground(vv.getBackground());
        if (font != null)
        {
            setFont(font);
        }
        else
        {
            setFont(vv.getFont());
        }
        setIcon(null);
        setBorder(noFocusBorder);
        setValue(value);
        return this;
    }
}