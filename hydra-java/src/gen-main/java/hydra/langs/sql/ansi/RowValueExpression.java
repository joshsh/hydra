package hydra.langs.sql.ansi;

import java.io.Serializable;

public class RowValueExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.RowValueExpression");
  
  public RowValueExpression () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof RowValueExpression)) {
      return false;
    }
    RowValueExpression o = (RowValueExpression) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}