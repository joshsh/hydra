package hydra.langs.tinkerpop.propertyGraph;

import java.io.Serializable;

/**
 * The type of a vertex
 */
public class VertexType<T> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/propertyGraph.VertexType");
  
  /**
   * The label of any vertex of this vertex type
   */
  public final hydra.langs.tinkerpop.propertyGraph.VertexLabel label;
  
  /**
   * The type of the id of any vertex of this vertex type
   */
  public final T id;
  
  /**
   * A list of property types. The types are ordered for the sake of applications in which property order is significant.
   */
  public final java.util.List<hydra.langs.tinkerpop.propertyGraph.PropertyType<T>> properties;
  
  public VertexType (hydra.langs.tinkerpop.propertyGraph.VertexLabel label, T id, java.util.List<hydra.langs.tinkerpop.propertyGraph.PropertyType<T>> properties) {
    this.label = label;
    this.id = id;
    this.properties = properties;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof VertexType)) {
      return false;
    }
    VertexType o = (VertexType) (other);
    return label.equals(o.label) && id.equals(o.id) && properties.equals(o.properties);
  }
  
  @Override
  public int hashCode() {
    return 2 * label.hashCode() + 3 * id.hashCode() + 5 * properties.hashCode();
  }
  
  public VertexType withLabel(hydra.langs.tinkerpop.propertyGraph.VertexLabel label) {
    return new VertexType(label, id, properties);
  }
  
  public VertexType withId(T id) {
    return new VertexType(label, id, properties);
  }
  
  public VertexType withProperties(java.util.List<hydra.langs.tinkerpop.propertyGraph.PropertyType<T>> properties) {
    return new VertexType(label, id, properties);
  }
}