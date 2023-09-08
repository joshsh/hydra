package hydra.langs.sql.ansi;

import java.io.Serializable;

public class CastSpecification implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.CastSpecification");
  
  public CastSpecification () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof CastSpecification)) {
      return false;
    }
    CastSpecification o = (CastSpecification) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}