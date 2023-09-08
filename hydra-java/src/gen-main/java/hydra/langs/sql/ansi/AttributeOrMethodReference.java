package hydra.langs.sql.ansi;

import java.io.Serializable;

public class AttributeOrMethodReference implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.AttributeOrMethodReference");
  
  public AttributeOrMethodReference () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof AttributeOrMethodReference)) {
      return false;
    }
    AttributeOrMethodReference o = (AttributeOrMethodReference) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}