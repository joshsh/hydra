package hydra.langs.sql.ansi;

import java.io.Serializable;

public class Subquery implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.Subquery");
  
  public final hydra.langs.sql.ansi.QueryExpression value;
  
  public Subquery (hydra.langs.sql.ansi.QueryExpression value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Subquery)) {
      return false;
    }
    Subquery o = (Subquery) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}