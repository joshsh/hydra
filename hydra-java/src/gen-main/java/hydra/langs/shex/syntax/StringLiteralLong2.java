package hydra.langs.shex.syntax;

import java.io.Serializable;

public class StringLiteralLong2 implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.StringLiteralLong2");
  
  public final java.util.List<hydra.langs.shex.syntax.StringLiteralLong2_Elmt> value;
  
  public StringLiteralLong2 (java.util.List<hydra.langs.shex.syntax.StringLiteralLong2_Elmt> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof StringLiteralLong2)) {
      return false;
    }
    StringLiteralLong2 o = (StringLiteralLong2) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}