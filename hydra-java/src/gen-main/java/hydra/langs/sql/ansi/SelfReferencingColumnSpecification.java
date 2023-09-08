package hydra.langs.sql.ansi;

import java.io.Serializable;

public class SelfReferencingColumnSpecification implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.SelfReferencingColumnSpecification");
  
  public SelfReferencingColumnSpecification () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SelfReferencingColumnSpecification)) {
      return false;
    }
    SelfReferencingColumnSpecification o = (SelfReferencingColumnSpecification) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}