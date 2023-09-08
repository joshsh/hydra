package hydra.langs.sql.ansi;

import java.io.Serializable;

public class BooleanType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.BooleanType");
  
  public BooleanType () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof BooleanType)) {
      return false;
    }
    BooleanType o = (BooleanType) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}