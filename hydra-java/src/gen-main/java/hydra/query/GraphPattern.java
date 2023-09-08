package hydra.query;

import java.io.Serializable;

/**
 * A query pattern which matches within a designated component subgraph
 */
public class GraphPattern<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/query.GraphPattern");
  
  /**
   * The name of the component graph
   */
  public final hydra.core.Name graph;
  
  /**
   * The patterns to match within the subgraph
   */
  public final java.util.List<hydra.query.Pattern<A>> patterns;
  
  public GraphPattern (hydra.core.Name graph, java.util.List<hydra.query.Pattern<A>> patterns) {
    this.graph = graph;
    this.patterns = patterns;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof GraphPattern)) {
      return false;
    }
    GraphPattern o = (GraphPattern) (other);
    return graph.equals(o.graph) && patterns.equals(o.patterns);
  }
  
  @Override
  public int hashCode() {
    return 2 * graph.hashCode() + 3 * patterns.hashCode();
  }
  
  public GraphPattern withGraph(hydra.core.Name graph) {
    return new GraphPattern(graph, patterns);
  }
  
  public GraphPattern withPatterns(java.util.List<hydra.query.Pattern<A>> patterns) {
    return new GraphPattern(graph, patterns);
  }
}