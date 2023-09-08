package hydra.langs.sql.ansi;

import java.io.Serializable;

public class ReferenceType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.ReferenceType");
  
  public ReferenceType () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ReferenceType)) {
      return false;
    }
    ReferenceType o = (ReferenceType) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}