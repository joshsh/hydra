package hydra.langs.shacl.model;

import java.io.Serializable;

/**
 * See https://www.w3.org/TR/shacl/#ClosedPatterConstraintComponent
 */
public class Closed implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shacl/model.Closed");
  
  public final Boolean isClosed;
  
  public final java.util.Optional<java.util.Set<hydra.langs.rdf.syntax.Property>> ignoredProperties;
  
  public Closed (Boolean isClosed, java.util.Optional<java.util.Set<hydra.langs.rdf.syntax.Property>> ignoredProperties) {
    this.isClosed = isClosed;
    this.ignoredProperties = ignoredProperties;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Closed)) {
      return false;
    }
    Closed o = (Closed) (other);
    return isClosed.equals(o.isClosed) && ignoredProperties.equals(o.ignoredProperties);
  }
  
  @Override
  public int hashCode() {
    return 2 * isClosed.hashCode() + 3 * ignoredProperties.hashCode();
  }
  
  public Closed withIsClosed(Boolean isClosed) {
    return new Closed(isClosed, ignoredProperties);
  }
  
  public Closed withIgnoredProperties(java.util.Optional<java.util.Set<hydra.langs.rdf.syntax.Property>> ignoredProperties) {
    return new Closed(isClosed, ignoredProperties);
  }
}