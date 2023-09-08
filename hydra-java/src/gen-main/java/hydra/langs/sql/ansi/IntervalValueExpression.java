package hydra.langs.sql.ansi;

import java.io.Serializable;

public class IntervalValueExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.IntervalValueExpression");
  
  public IntervalValueExpression () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof IntervalValueExpression)) {
      return false;
    }
    IntervalValueExpression o = (IntervalValueExpression) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}