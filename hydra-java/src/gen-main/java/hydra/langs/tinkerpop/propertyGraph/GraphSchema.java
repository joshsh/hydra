package hydra.langs.tinkerpop.propertyGraph;

import java.io.Serializable;

/**
 * A graph schema; a vertex and edge types for the vertices and edges of a graph conforming to the schema
 */
public class GraphSchema<T> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/propertyGraph.GraphSchema");
  
  /**
   * A unique vertex type for each vertex label which may occur in a graph
   */
  public final java.util.Map<hydra.langs.tinkerpop.propertyGraph.VertexLabel, hydra.langs.tinkerpop.propertyGraph.VertexType<T>> vertices;
  
  /**
   * A unique edge type for each edge label which may occur in a graph
   */
  public final java.util.Map<hydra.langs.tinkerpop.propertyGraph.EdgeLabel, hydra.langs.tinkerpop.propertyGraph.EdgeType<T>> edges;
  
  public GraphSchema (java.util.Map<hydra.langs.tinkerpop.propertyGraph.VertexLabel, hydra.langs.tinkerpop.propertyGraph.VertexType<T>> vertices, java.util.Map<hydra.langs.tinkerpop.propertyGraph.EdgeLabel, hydra.langs.tinkerpop.propertyGraph.EdgeType<T>> edges) {
    this.vertices = vertices;
    this.edges = edges;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof GraphSchema)) {
      return false;
    }
    GraphSchema o = (GraphSchema) (other);
    return vertices.equals(o.vertices) && edges.equals(o.edges);
  }
  
  @Override
  public int hashCode() {
    return 2 * vertices.hashCode() + 3 * edges.hashCode();
  }
  
  public GraphSchema withVertices(java.util.Map<hydra.langs.tinkerpop.propertyGraph.VertexLabel, hydra.langs.tinkerpop.propertyGraph.VertexType<T>> vertices) {
    return new GraphSchema(vertices, edges);
  }
  
  public GraphSchema withEdges(java.util.Map<hydra.langs.tinkerpop.propertyGraph.EdgeLabel, hydra.langs.tinkerpop.propertyGraph.EdgeType<T>> edges) {
    return new GraphSchema(vertices, edges);
  }
}