// Note: this is an automatically generated file. Do not edit.

package hydra.langs.tinkerpop.queries;

import java.io.Serializable;

public class VertexPattern implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/queries.VertexPattern");
  
  public final hydra.util.Opt<hydra.langs.tinkerpop.queries.Variable> variable;
  
  public final hydra.util.Opt<hydra.langs.tinkerpop.propertyGraph.VertexLabel> label;
  
  public final java.util.List<hydra.langs.tinkerpop.queries.PropertyPattern> properties;
  
  public final java.util.List<hydra.langs.tinkerpop.queries.EdgeProjectionPattern> edges;
  
  public VertexPattern (hydra.util.Opt<hydra.langs.tinkerpop.queries.Variable> variable, hydra.util.Opt<hydra.langs.tinkerpop.propertyGraph.VertexLabel> label, java.util.List<hydra.langs.tinkerpop.queries.PropertyPattern> properties, java.util.List<hydra.langs.tinkerpop.queries.EdgeProjectionPattern> edges) {
    if (variable == null) {
      throw new IllegalArgumentException("null value for 'variable' argument");
    }
    if (label == null) {
      throw new IllegalArgumentException("null value for 'label' argument");
    }
    if (properties == null) {
      throw new IllegalArgumentException("null value for 'properties' argument");
    }
    if (edges == null) {
      throw new IllegalArgumentException("null value for 'edges' argument");
    }
    this.variable = variable;
    this.label = label;
    this.properties = properties;
    this.edges = edges;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof VertexPattern)) {
      return false;
    }
    VertexPattern o = (VertexPattern) (other);
    return variable.equals(o.variable) && label.equals(o.label) && properties.equals(o.properties) && edges.equals(o.edges);
  }
  
  @Override
  public int hashCode() {
    return 2 * variable.hashCode() + 3 * label.hashCode() + 5 * properties.hashCode() + 7 * edges.hashCode();
  }
  
  public VertexPattern withVariable(hydra.util.Opt<hydra.langs.tinkerpop.queries.Variable> variable) {
    if (variable == null) {
      throw new IllegalArgumentException("null value for 'variable' argument");
    }
    return new VertexPattern(variable, label, properties, edges);
  }
  
  public VertexPattern withLabel(hydra.util.Opt<hydra.langs.tinkerpop.propertyGraph.VertexLabel> label) {
    if (label == null) {
      throw new IllegalArgumentException("null value for 'label' argument");
    }
    return new VertexPattern(variable, label, properties, edges);
  }
  
  public VertexPattern withProperties(java.util.List<hydra.langs.tinkerpop.queries.PropertyPattern> properties) {
    if (properties == null) {
      throw new IllegalArgumentException("null value for 'properties' argument");
    }
    return new VertexPattern(variable, label, properties, edges);
  }
  
  public VertexPattern withEdges(java.util.List<hydra.langs.tinkerpop.queries.EdgeProjectionPattern> edges) {
    if (edges == null) {
      throw new IllegalArgumentException("null value for 'edges' argument");
    }
    return new VertexPattern(variable, label, properties, edges);
  }
}