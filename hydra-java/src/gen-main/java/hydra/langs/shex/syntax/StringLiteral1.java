package hydra.langs.shex.syntax;

import java.io.Serializable;

public class StringLiteral1 implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.StringLiteral1");
  
  public final java.util.List<hydra.langs.shex.syntax.StringLiteral1_Elmt> value;
  
  public StringLiteral1 (java.util.List<hydra.langs.shex.syntax.StringLiteral1_Elmt> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof StringLiteral1)) {
      return false;
    }
    StringLiteral1 o = (StringLiteral1) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}