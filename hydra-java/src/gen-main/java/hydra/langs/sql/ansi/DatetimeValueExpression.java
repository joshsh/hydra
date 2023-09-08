package hydra.langs.sql.ansi;

import java.io.Serializable;

public class DatetimeValueExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.DatetimeValueExpression");
  
  public DatetimeValueExpression () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DatetimeValueExpression)) {
      return false;
    }
    DatetimeValueExpression o = (DatetimeValueExpression) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}