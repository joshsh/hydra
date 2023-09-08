package hydra.langs.sql.ansi;

import java.io.Serializable;

public class TableName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.TableName");
  
  public final String value;
  
  public TableName (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TableName)) {
      return false;
    }
    TableName o = (TableName) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}