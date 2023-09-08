package hydra.langs.sql.ansi;

import java.io.Serializable;

public class ArrayType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.ArrayType");
  
  public ArrayType () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ArrayType)) {
      return false;
    }
    ArrayType o = (ArrayType) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}