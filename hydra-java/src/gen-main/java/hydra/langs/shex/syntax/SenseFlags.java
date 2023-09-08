package hydra.langs.shex.syntax;

import java.io.Serializable;

public class SenseFlags implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.SenseFlags");
  
  public SenseFlags () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SenseFlags)) {
      return false;
    }
    SenseFlags o = (SenseFlags) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}