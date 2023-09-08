package hydra.langs.sql.ansi;

import java.io.Serializable;

public class InsertColumnList implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.InsertColumnList");
  
  public final hydra.langs.sql.ansi.ColumnNameList value;
  
  public InsertColumnList (hydra.langs.sql.ansi.ColumnNameList value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof InsertColumnList)) {
      return false;
    }
    InsertColumnList o = (InsertColumnList) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}