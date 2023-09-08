package hydra.langs.sql.ansi;

import java.io.Serializable;

public class MethodInvocation implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.MethodInvocation");
  
  public MethodInvocation () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof MethodInvocation)) {
      return false;
    }
    MethodInvocation o = (MethodInvocation) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}