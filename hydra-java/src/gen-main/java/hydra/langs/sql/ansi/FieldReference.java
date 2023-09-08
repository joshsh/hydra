package hydra.langs.sql.ansi;

import java.io.Serializable;

public class FieldReference implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.FieldReference");
  
  public FieldReference () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof FieldReference)) {
      return false;
    }
    FieldReference o = (FieldReference) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}