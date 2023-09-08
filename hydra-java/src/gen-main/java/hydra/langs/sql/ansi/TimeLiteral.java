package hydra.langs.sql.ansi;

import java.io.Serializable;

public class TimeLiteral implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.TimeLiteral");
  
  public final hydra.langs.sql.ansi.TimeString value;
  
  public TimeLiteral (hydra.langs.sql.ansi.TimeString value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TimeLiteral)) {
      return false;
    }
    TimeLiteral o = (TimeLiteral) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}