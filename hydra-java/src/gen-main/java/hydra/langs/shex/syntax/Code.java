package hydra.langs.shex.syntax;

import java.io.Serializable;

public class Code implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.Code");
  
  public final java.util.List<hydra.langs.shex.syntax.Code_Elmt> value;
  
  public Code (java.util.List<hydra.langs.shex.syntax.Code_Elmt> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Code)) {
      return false;
    }
    Code o = (Code) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}