package hydra.langs.tinkerpop.propertyGraph;

import java.io.Serializable;

/**
 * An edge
 */
public class Edge<V> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/propertyGraph.Edge");
  
  /**
   * The label of the edge
   */
  public final hydra.langs.tinkerpop.propertyGraph.EdgeLabel label;
  
  /**
   * The unique identifier of the edge
   */
  public final V id;
  
  /**
   * The id of the out-vertex (tail) of the edge
   */
  public final V out;
  
  /**
   * The id of the in-vertex (head) of the edge
   */
  public final V in;
  
  /**
   * A key/value map of edge properties
   */
  public final java.util.Map<hydra.langs.tinkerpop.propertyGraph.PropertyKey, V> properties;
  
  public Edge (hydra.langs.tinkerpop.propertyGraph.EdgeLabel label, V id, V out, V in, java.util.Map<hydra.langs.tinkerpop.propertyGraph.PropertyKey, V> properties) {
    this.label = label;
    this.id = id;
    this.out = out;
    this.in = in;
    this.properties = properties;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Edge)) {
      return false;
    }
    Edge o = (Edge) (other);
    return label.equals(o.label) && id.equals(o.id) && out.equals(o.out) && in.equals(o.in) && properties.equals(o.properties);
  }
  
  @Override
  public int hashCode() {
    return 2 * label.hashCode() + 3 * id.hashCode() + 5 * out.hashCode() + 7 * in.hashCode() + 11 * properties.hashCode();
  }
  
  public Edge withLabel(hydra.langs.tinkerpop.propertyGraph.EdgeLabel label) {
    return new Edge(label, id, out, in, properties);
  }
  
  public Edge withId(V id) {
    return new Edge(label, id, out, in, properties);
  }
  
  public Edge withOut(V out) {
    return new Edge(label, id, out, in, properties);
  }
  
  public Edge withIn(V in) {
    return new Edge(label, id, out, in, properties);
  }
  
  public Edge withProperties(java.util.Map<hydra.langs.tinkerpop.propertyGraph.PropertyKey, V> properties) {
    return new Edge(label, id, out, in, properties);
  }
}