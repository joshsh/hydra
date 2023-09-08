package hydra.langs.shex.syntax;

import java.io.Serializable;

public class StringLiteral2 implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.StringLiteral2");
  
  public final java.util.List<hydra.langs.shex.syntax.StringLiteral2_Elmt> value;
  
  public StringLiteral2 (java.util.List<hydra.langs.shex.syntax.StringLiteral2_Elmt> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof StringLiteral2)) {
      return false;
    }
    StringLiteral2 o = (StringLiteral2) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}