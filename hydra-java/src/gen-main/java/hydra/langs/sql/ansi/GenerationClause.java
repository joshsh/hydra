package hydra.langs.sql.ansi;

import java.io.Serializable;

public class GenerationClause implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.GenerationClause");
  
  public GenerationClause () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof GenerationClause)) {
      return false;
    }
    GenerationClause o = (GenerationClause) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}