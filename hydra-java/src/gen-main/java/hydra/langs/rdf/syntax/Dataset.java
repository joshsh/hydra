package hydra.langs.rdf.syntax;

import java.io.Serializable;

public class Dataset implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/rdf/syntax.Dataset");
  
  public final java.util.Set<hydra.langs.rdf.syntax.Quad> value;
  
  public Dataset (java.util.Set<hydra.langs.rdf.syntax.Quad> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Dataset)) {
      return false;
    }
    Dataset o = (Dataset) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}