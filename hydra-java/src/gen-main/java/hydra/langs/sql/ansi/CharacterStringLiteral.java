package hydra.langs.sql.ansi;

import java.io.Serializable;

public class CharacterStringLiteral implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.CharacterStringLiteral");
  
  public final String value;
  
  public CharacterStringLiteral (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof CharacterStringLiteral)) {
      return false;
    }
    CharacterStringLiteral o = (CharacterStringLiteral) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}