package hydra.langs.sql.ansi;

import java.io.Serializable;

public class FromSubquery implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.FromSubquery");
  
  public FromSubquery () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof FromSubquery)) {
      return false;
    }
    FromSubquery o = (FromSubquery) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}