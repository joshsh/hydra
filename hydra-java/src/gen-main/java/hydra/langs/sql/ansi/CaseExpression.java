package hydra.langs.sql.ansi;

import java.io.Serializable;

public class CaseExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.CaseExpression");
  
  public CaseExpression () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof CaseExpression)) {
      return false;
    }
    CaseExpression o = (CaseExpression) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}