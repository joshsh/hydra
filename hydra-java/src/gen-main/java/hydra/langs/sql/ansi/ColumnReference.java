package hydra.langs.sql.ansi;

import java.io.Serializable;

public class ColumnReference implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.ColumnReference");
  
  public ColumnReference () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ColumnReference)) {
      return false;
    }
    ColumnReference o = (ColumnReference) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}