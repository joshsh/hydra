package hydra.langs.tinkerpop.features;

import java.io.Serializable;

/**
 * An interface that represents the capabilities of a Graph implementation. By default all methods of features return true and it is up to implementers to disable feature they don't support. Users should check features prior to using various functions of TinkerPop to help ensure code portability across implementations. For example, a common usage would be to check if a graph supports transactions prior to calling the commit method on Graph.tx().
 * 
 * As an additional notice to Graph Providers, feature methods will be used by the test suite to determine which tests will be ignored and which will be executed, therefore proper setting of these features is essential to maximizing the amount of testing performed by the suite. Further note, that these methods may be called by the TinkerPop core code to determine what operations may be appropriately executed which will have impact on features utilized by users.
 */
public class Features implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/features.Features");
  
  /**
   * Gets the features related to edge operation.
   */
  public final hydra.langs.tinkerpop.features.EdgeFeatures edge;
  
  /**
   * Gets the features related to graph operation.
   */
  public final hydra.langs.tinkerpop.features.GraphFeatures graph;
  
  /**
   * Gets the features related to vertex operation.
   */
  public final hydra.langs.tinkerpop.features.VertexFeatures vertex;
  
  public Features (hydra.langs.tinkerpop.features.EdgeFeatures edge, hydra.langs.tinkerpop.features.GraphFeatures graph, hydra.langs.tinkerpop.features.VertexFeatures vertex) {
    this.edge = edge;
    this.graph = graph;
    this.vertex = vertex;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Features)) {
      return false;
    }
    Features o = (Features) (other);
    return edge.equals(o.edge) && graph.equals(o.graph) && vertex.equals(o.vertex);
  }
  
  @Override
  public int hashCode() {
    return 2 * edge.hashCode() + 3 * graph.hashCode() + 5 * vertex.hashCode();
  }
  
  public Features withEdge(hydra.langs.tinkerpop.features.EdgeFeatures edge) {
    return new Features(edge, graph, vertex);
  }
  
  public Features withGraph(hydra.langs.tinkerpop.features.GraphFeatures graph) {
    return new Features(edge, graph, vertex);
  }
  
  public Features withVertex(hydra.langs.tinkerpop.features.VertexFeatures vertex) {
    return new Features(edge, graph, vertex);
  }
}