package hydra.langs.sql.ansi;

import java.io.Serializable;

public class IntervalType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.IntervalType");
  
  public IntervalType () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof IntervalType)) {
      return false;
    }
    IntervalType o = (IntervalType) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}