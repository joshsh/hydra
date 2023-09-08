package hydra.langs.tinkerpop.propertyGraph;

import java.io.Serializable;

/**
 * The type of an edge
 */
public class EdgeType<T> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/propertyGraph.EdgeType");
  
  /**
   * The label of any edge of this edge type
   */
  public final hydra.langs.tinkerpop.propertyGraph.EdgeLabel label;
  
  /**
   * The type of the id of any edge of this edge type
   */
  public final T id;
  
  /**
   * The label of the out-vertex (tail) of any edge of this edge type
   */
  public final hydra.langs.tinkerpop.propertyGraph.VertexLabel out;
  
  /**
   * The label of the in-vertex (head) of any edge of this edge type
   */
  public final hydra.langs.tinkerpop.propertyGraph.VertexLabel in;
  
  /**
   * A list of property types. The types are ordered for the sake of applications in which property order is significant.
   */
  public final java.util.List<hydra.langs.tinkerpop.propertyGraph.PropertyType<T>> properties;
  
  public EdgeType (hydra.langs.tinkerpop.propertyGraph.EdgeLabel label, T id, hydra.langs.tinkerpop.propertyGraph.VertexLabel out, hydra.langs.tinkerpop.propertyGraph.VertexLabel in, java.util.List<hydra.langs.tinkerpop.propertyGraph.PropertyType<T>> properties) {
    this.label = label;
    this.id = id;
    this.out = out;
    this.in = in;
    this.properties = properties;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EdgeType)) {
      return false;
    }
    EdgeType o = (EdgeType) (other);
    return label.equals(o.label) && id.equals(o.id) && out.equals(o.out) && in.equals(o.in) && properties.equals(o.properties);
  }
  
  @Override
  public int hashCode() {
    return 2 * label.hashCode() + 3 * id.hashCode() + 5 * out.hashCode() + 7 * in.hashCode() + 11 * properties.hashCode();
  }
  
  public EdgeType withLabel(hydra.langs.tinkerpop.propertyGraph.EdgeLabel label) {
    return new EdgeType(label, id, out, in, properties);
  }
  
  public EdgeType withId(T id) {
    return new EdgeType(label, id, out, in, properties);
  }
  
  public EdgeType withOut(hydra.langs.tinkerpop.propertyGraph.VertexLabel out) {
    return new EdgeType(label, id, out, in, properties);
  }
  
  public EdgeType withIn(hydra.langs.tinkerpop.propertyGraph.VertexLabel in) {
    return new EdgeType(label, id, out, in, properties);
  }
  
  public EdgeType withProperties(java.util.List<hydra.langs.tinkerpop.propertyGraph.PropertyType<T>> properties) {
    return new EdgeType(label, id, out, in, properties);
  }
}