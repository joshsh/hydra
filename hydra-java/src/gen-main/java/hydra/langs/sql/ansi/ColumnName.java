package hydra.langs.sql.ansi;

import java.io.Serializable;

public class ColumnName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.ColumnName");
  
  public final String value;
  
  public ColumnName (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ColumnName)) {
      return false;
    }
    ColumnName o = (ColumnName) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}