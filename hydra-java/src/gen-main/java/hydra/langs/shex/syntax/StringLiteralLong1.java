package hydra.langs.shex.syntax;

import java.io.Serializable;

public class StringLiteralLong1 implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.StringLiteralLong1");
  
  public final java.util.List<hydra.langs.shex.syntax.StringLiteralLong1_Elmt> value;
  
  public StringLiteralLong1 (java.util.List<hydra.langs.shex.syntax.StringLiteralLong1_Elmt> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof StringLiteralLong1)) {
      return false;
    }
    StringLiteralLong1 o = (StringLiteralLong1) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}