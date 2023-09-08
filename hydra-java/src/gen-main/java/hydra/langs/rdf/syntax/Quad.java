package hydra.langs.rdf.syntax;

import java.io.Serializable;

/**
 * An RDF triple with an optional named graph component
 */
public class Quad implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/rdf/syntax.Quad");
  
  public final hydra.langs.rdf.syntax.Resource subject;
  
  public final hydra.langs.rdf.syntax.Iri predicate;
  
  public final hydra.langs.rdf.syntax.Node object;
  
  public final java.util.Optional<hydra.langs.rdf.syntax.Iri> graph;
  
  public Quad (hydra.langs.rdf.syntax.Resource subject, hydra.langs.rdf.syntax.Iri predicate, hydra.langs.rdf.syntax.Node object, java.util.Optional<hydra.langs.rdf.syntax.Iri> graph) {
    this.subject = subject;
    this.predicate = predicate;
    this.object = object;
    this.graph = graph;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Quad)) {
      return false;
    }
    Quad o = (Quad) (other);
    return subject.equals(o.subject) && predicate.equals(o.predicate) && object.equals(o.object) && graph.equals(o.graph);
  }
  
  @Override
  public int hashCode() {
    return 2 * subject.hashCode() + 3 * predicate.hashCode() + 5 * object.hashCode() + 7 * graph.hashCode();
  }
  
  public Quad withSubject(hydra.langs.rdf.syntax.Resource subject) {
    return new Quad(subject, predicate, object, graph);
  }
  
  public Quad withPredicate(hydra.langs.rdf.syntax.Iri predicate) {
    return new Quad(subject, predicate, object, graph);
  }
  
  public Quad withObject(hydra.langs.rdf.syntax.Node object) {
    return new Quad(subject, predicate, object, graph);
  }
  
  public Quad withGraph(java.util.Optional<hydra.langs.rdf.syntax.Iri> graph) {
    return new Quad(subject, predicate, object, graph);
  }
}