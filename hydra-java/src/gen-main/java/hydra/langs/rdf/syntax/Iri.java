package hydra.langs.rdf.syntax;

import java.io.Serializable;

/**
 * An Internationalized Resource Identifier
 */
public class Iri implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/rdf/syntax.Iri");
  
  /**
   * An Internationalized Resource Identifier
   */
  public final String value;
  
  public Iri (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Iri)) {
      return false;
    }
    Iri o = (Iri) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}