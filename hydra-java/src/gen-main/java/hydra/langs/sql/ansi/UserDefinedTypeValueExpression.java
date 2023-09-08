package hydra.langs.sql.ansi;

import java.io.Serializable;

public class UserDefinedTypeValueExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.UserDefinedTypeValueExpression");
  
  public final hydra.langs.sql.ansi.ValueExpressionPrimary value;
  
  public UserDefinedTypeValueExpression (hydra.langs.sql.ansi.ValueExpressionPrimary value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof UserDefinedTypeValueExpression)) {
      return false;
    }
    UserDefinedTypeValueExpression o = (UserDefinedTypeValueExpression) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}