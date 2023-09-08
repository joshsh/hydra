package hydra.langs.tinkerpop.propertyGraph;

import java.io.Serializable;

/**
 * A graph; a self-contained collection of vertices and edges
 */
public class Graph<V> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/propertyGraph.Graph");
  
  public final java.util.Map<V, hydra.langs.tinkerpop.propertyGraph.Vertex<V>> vertices;
  
  public final java.util.Map<V, hydra.langs.tinkerpop.propertyGraph.Edge<V>> edges;
  
  public Graph (java.util.Map<V, hydra.langs.tinkerpop.propertyGraph.Vertex<V>> vertices, java.util.Map<V, hydra.langs.tinkerpop.propertyGraph.Edge<V>> edges) {
    this.vertices = vertices;
    this.edges = edges;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Graph)) {
      return false;
    }
    Graph o = (Graph) (other);
    return vertices.equals(o.vertices) && edges.equals(o.edges);
  }
  
  @Override
  public int hashCode() {
    return 2 * vertices.hashCode() + 3 * edges.hashCode();
  }
  
  public Graph withVertices(java.util.Map<V, hydra.langs.tinkerpop.propertyGraph.Vertex<V>> vertices) {
    return new Graph(vertices, edges);
  }
  
  public Graph withEdges(java.util.Map<V, hydra.langs.tinkerpop.propertyGraph.Edge<V>> edges) {
    return new Graph(vertices, edges);
  }
}