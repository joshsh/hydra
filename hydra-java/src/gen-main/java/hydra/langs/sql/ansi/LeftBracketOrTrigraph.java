package hydra.langs.sql.ansi;

import java.io.Serializable;

public class LeftBracketOrTrigraph implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.LeftBracketOrTrigraph");
  
  public final String value;
  
  public LeftBracketOrTrigraph (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof LeftBracketOrTrigraph)) {
      return false;
    }
    LeftBracketOrTrigraph o = (LeftBracketOrTrigraph) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}