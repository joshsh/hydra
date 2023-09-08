package hydra.langs.sql.ansi;

import java.io.Serializable;

public class NewSpecification implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.NewSpecification");
  
  public NewSpecification () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof NewSpecification)) {
      return false;
    }
    NewSpecification o = (NewSpecification) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}