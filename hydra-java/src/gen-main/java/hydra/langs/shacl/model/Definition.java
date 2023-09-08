package hydra.langs.shacl.model;

import java.io.Serializable;

/**
 * An instance of a type like sh:Shape or sh:NodeShape, together with a unique IRI for that instance
 */
public class Definition<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shacl/model.Definition");
  
  public final hydra.langs.rdf.syntax.Iri iri;
  
  public final A target;
  
  public Definition (hydra.langs.rdf.syntax.Iri iri, A target) {
    this.iri = iri;
    this.target = target;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Definition)) {
      return false;
    }
    Definition o = (Definition) (other);
    return iri.equals(o.iri) && target.equals(o.target);
  }
  
  @Override
  public int hashCode() {
    return 2 * iri.hashCode() + 3 * target.hashCode();
  }
  
  public Definition withIri(hydra.langs.rdf.syntax.Iri iri) {
    return new Definition(iri, target);
  }
  
  public Definition withTarget(A target) {
    return new Definition(iri, target);
  }
}