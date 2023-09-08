package hydra.langs.sql.ansi;

import java.io.Serializable;

public class NumericValueExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.NumericValueExpression");
  
  public NumericValueExpression () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof NumericValueExpression)) {
      return false;
    }
    NumericValueExpression o = (NumericValueExpression) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}