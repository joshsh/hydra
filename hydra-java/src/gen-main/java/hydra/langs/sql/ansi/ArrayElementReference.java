package hydra.langs.sql.ansi;

import java.io.Serializable;

public class ArrayElementReference implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.ArrayElementReference");
  
  public ArrayElementReference () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ArrayElementReference)) {
      return false;
    }
    ArrayElementReference o = (ArrayElementReference) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}