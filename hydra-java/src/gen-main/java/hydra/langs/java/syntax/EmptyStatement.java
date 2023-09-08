package hydra.langs.java.syntax;

import java.io.Serializable;

public class EmptyStatement implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.EmptyStatement");
  
  public EmptyStatement () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EmptyStatement)) {
      return false;
    }
    EmptyStatement o = (EmptyStatement) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}