package hydra.langs.sql.ansi;

import java.io.Serializable;

public class RightBracketOrTrigraph implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.RightBracketOrTrigraph");
  
  public final String value;
  
  public RightBracketOrTrigraph (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof RightBracketOrTrigraph)) {
      return false;
    }
    RightBracketOrTrigraph o = (RightBracketOrTrigraph) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}