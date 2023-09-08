package hydra.langs.sql.ansi;

import java.io.Serializable;

public class FromDefault implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.FromDefault");
  
  public FromDefault () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof FromDefault)) {
      return false;
    }
    FromDefault o = (FromDefault) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}