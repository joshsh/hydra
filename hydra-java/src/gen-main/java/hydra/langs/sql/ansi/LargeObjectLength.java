package hydra.langs.sql.ansi;

import java.io.Serializable;

public class LargeObjectLength implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.LargeObjectLength");
  
  public LargeObjectLength () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof LargeObjectLength)) {
      return false;
    }
    LargeObjectLength o = (LargeObjectLength) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}