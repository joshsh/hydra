package hydra.phantoms;

import java.io.Serializable;

/**
 * An association of a field name (as in a case statement) with a phantom type
 */
public class Case<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/phantoms.Case");
  
  public final hydra.core.FieldName value;
  
  public Case (hydra.core.FieldName value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Case)) {
      return false;
    }
    Case o = (Case) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}