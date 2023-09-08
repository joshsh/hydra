package hydra.langs.sql.ansi;

import java.io.Serializable;

public class RoutineInvocation implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.RoutineInvocation");
  
  public RoutineInvocation () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof RoutineInvocation)) {
      return false;
    }
    RoutineInvocation o = (RoutineInvocation) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}