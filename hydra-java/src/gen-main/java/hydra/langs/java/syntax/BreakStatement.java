package hydra.langs.java.syntax;

import java.io.Serializable;

public class BreakStatement implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.BreakStatement");
  
  public final java.util.Optional<hydra.langs.java.syntax.Identifier> value;
  
  public BreakStatement (java.util.Optional<hydra.langs.java.syntax.Identifier> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof BreakStatement)) {
      return false;
    }
    BreakStatement o = (BreakStatement) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}