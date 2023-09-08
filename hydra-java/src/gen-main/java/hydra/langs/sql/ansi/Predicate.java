package hydra.langs.sql.ansi;

import java.io.Serializable;

public class Predicate implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.Predicate");
  
  public Predicate () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Predicate)) {
      return false;
    }
    Predicate o = (Predicate) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}