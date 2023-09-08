package hydra.langs.sql.ansi;

import java.io.Serializable;

public class CharacterSetSpecification implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.CharacterSetSpecification");
  
  public CharacterSetSpecification () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof CharacterSetSpecification)) {
      return false;
    }
    CharacterSetSpecification o = (CharacterSetSpecification) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}