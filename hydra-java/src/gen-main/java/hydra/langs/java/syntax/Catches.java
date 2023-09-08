package hydra.langs.java.syntax;

import java.io.Serializable;

public class Catches implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.Catches");
  
  public final java.util.List<hydra.langs.java.syntax.CatchClause> value;
  
  public Catches (java.util.List<hydra.langs.java.syntax.CatchClause> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Catches)) {
      return false;
    }
    Catches o = (Catches) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}