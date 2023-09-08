package hydra.langs.shex.syntax;

import java.io.Serializable;

public class Include implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.Include");
  
  public final hydra.langs.shex.syntax.TripleExprLabel value;
  
  public Include (hydra.langs.shex.syntax.TripleExprLabel value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Include)) {
      return false;
    }
    Include o = (Include) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}