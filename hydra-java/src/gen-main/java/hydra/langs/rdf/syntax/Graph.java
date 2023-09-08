package hydra.langs.rdf.syntax;

import java.io.Serializable;

public class Graph implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/rdf/syntax.Graph");
  
  public final java.util.Set<hydra.langs.rdf.syntax.Triple> value;
  
  public Graph (java.util.Set<hydra.langs.rdf.syntax.Triple> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Graph)) {
      return false;
    }
    Graph o = (Graph) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}