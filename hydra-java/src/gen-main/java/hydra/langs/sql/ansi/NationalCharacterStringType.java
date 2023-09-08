package hydra.langs.sql.ansi;

import java.io.Serializable;

public class NationalCharacterStringType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.NationalCharacterStringType");
  
  public NationalCharacterStringType () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof NationalCharacterStringType)) {
      return false;
    }
    NationalCharacterStringType o = (NationalCharacterStringType) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}