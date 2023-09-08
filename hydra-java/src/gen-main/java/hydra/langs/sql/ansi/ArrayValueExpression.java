package hydra.langs.sql.ansi;

import java.io.Serializable;

public class ArrayValueExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.ArrayValueExpression");
  
  public ArrayValueExpression () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ArrayValueExpression)) {
      return false;
    }
    ArrayValueExpression o = (ArrayValueExpression) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}