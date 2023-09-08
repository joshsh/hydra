package hydra.langs.rdf.syntax;

import java.io.Serializable;

/**
 * A graph of RDF statements together with a distinguished subject and/or object node
 */
public class Description implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/rdf/syntax.Description");
  
  public final hydra.langs.rdf.syntax.Node subject;
  
  public final hydra.langs.rdf.syntax.Graph graph;
  
  public Description (hydra.langs.rdf.syntax.Node subject, hydra.langs.rdf.syntax.Graph graph) {
    this.subject = subject;
    this.graph = graph;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Description)) {
      return false;
    }
    Description o = (Description) (other);
    return subject.equals(o.subject) && graph.equals(o.graph);
  }
  
  @Override
  public int hashCode() {
    return 2 * subject.hashCode() + 3 * graph.hashCode();
  }
  
  public Description withSubject(hydra.langs.rdf.syntax.Node subject) {
    return new Description(subject, graph);
  }
  
  public Description withGraph(hydra.langs.rdf.syntax.Graph graph) {
    return new Description(subject, graph);
  }
}