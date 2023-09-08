package hydra.langs.sql.ansi;

import java.io.Serializable;

public class ColumnConstraintDefinition implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.ColumnConstraintDefinition");
  
  public ColumnConstraintDefinition () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ColumnConstraintDefinition)) {
      return false;
    }
    ColumnConstraintDefinition o = (ColumnConstraintDefinition) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}