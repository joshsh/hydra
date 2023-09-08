package hydra.langs.sql.ansi;

import java.io.Serializable;

public class AsSubqueryClause implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.AsSubqueryClause");
  
  public AsSubqueryClause () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof AsSubqueryClause)) {
      return false;
    }
    AsSubqueryClause o = (AsSubqueryClause) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}