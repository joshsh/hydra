package hydra.langs.sql.ansi;

import java.io.Serializable;

public class StringValueExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.StringValueExpression");
  
  public StringValueExpression () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof StringValueExpression)) {
      return false;
    }
    StringValueExpression o = (StringValueExpression) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}