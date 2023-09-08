package hydra.langs.sql.ansi;

import java.io.Serializable;

public class NextValueExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.NextValueExpression");
  
  public NextValueExpression () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof NextValueExpression)) {
      return false;
    }
    NextValueExpression o = (NextValueExpression) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}