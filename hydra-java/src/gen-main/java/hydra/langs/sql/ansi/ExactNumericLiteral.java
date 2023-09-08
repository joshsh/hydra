package hydra.langs.sql.ansi;

import java.io.Serializable;

public class ExactNumericLiteral implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.ExactNumericLiteral");
  
  public final String value;
  
  public ExactNumericLiteral (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ExactNumericLiteral)) {
      return false;
    }
    ExactNumericLiteral o = (ExactNumericLiteral) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}