package hydra.langs.shex.syntax;

import java.io.Serializable;

public class Exclusion implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.Exclusion");
  
  public final hydra.langs.shex.syntax.Iri value;
  
  public Exclusion (hydra.langs.shex.syntax.Iri value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Exclusion)) {
      return false;
    }
    Exclusion o = (Exclusion) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}