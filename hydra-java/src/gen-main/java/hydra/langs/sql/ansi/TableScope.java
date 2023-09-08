package hydra.langs.sql.ansi;

import java.io.Serializable;

public class TableScope implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.TableScope");
  
  public final hydra.langs.sql.ansi.GlobalOrLocal value;
  
  public TableScope (hydra.langs.sql.ansi.GlobalOrLocal value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TableScope)) {
      return false;
    }
    TableScope o = (TableScope) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}