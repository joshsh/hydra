package hydra.langs.sql.ansi;

import java.io.Serializable;

public class ColumnOptions implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.ColumnOptions");
  
  public ColumnOptions () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ColumnOptions)) {
      return false;
    }
    ColumnOptions o = (ColumnOptions) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}