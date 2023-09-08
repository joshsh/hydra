package hydra.langs.sql.ansi;

import java.io.Serializable;

public class MultisetElementReference implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.MultisetElementReference");
  
  public MultisetElementReference () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof MultisetElementReference)) {
      return false;
    }
    MultisetElementReference o = (MultisetElementReference) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}