package hydra.langs.sql.ansi;

import java.io.Serializable;

public class BooleanPredicand implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.BooleanPredicand");
  
  public BooleanPredicand () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof BooleanPredicand)) {
      return false;
    }
    BooleanPredicand o = (BooleanPredicand) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}