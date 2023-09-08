package hydra.langs.shex.syntax;

import java.io.Serializable;

public class IncludeSet implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.IncludeSet");
  
  public final java.util.List<hydra.langs.shex.syntax.ShapeExprLabel> value;
  
  public IncludeSet (java.util.List<hydra.langs.shex.syntax.ShapeExprLabel> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof IncludeSet)) {
      return false;
    }
    IncludeSet o = (IncludeSet) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}