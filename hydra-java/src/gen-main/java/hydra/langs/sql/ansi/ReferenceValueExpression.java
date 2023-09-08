package hydra.langs.sql.ansi;

import java.io.Serializable;

public class ReferenceValueExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.ReferenceValueExpression");
  
  public final hydra.langs.sql.ansi.ValueExpressionPrimary value;
  
  public ReferenceValueExpression (hydra.langs.sql.ansi.ValueExpressionPrimary value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ReferenceValueExpression)) {
      return false;
    }
    ReferenceValueExpression o = (ReferenceValueExpression) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}