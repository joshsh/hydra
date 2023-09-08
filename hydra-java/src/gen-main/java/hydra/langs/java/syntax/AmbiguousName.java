package hydra.langs.java.syntax;

import java.io.Serializable;

public class AmbiguousName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.AmbiguousName");
  
  public final java.util.List<hydra.langs.java.syntax.Identifier> value;
  
  public AmbiguousName (java.util.List<hydra.langs.java.syntax.Identifier> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof AmbiguousName)) {
      return false;
    }
    AmbiguousName o = (AmbiguousName) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}