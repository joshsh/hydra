package hydra.langs.owl.syntax;

import java.io.Serializable;

public class InverseObjectProperty implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.InverseObjectProperty");
  
  public final hydra.langs.owl.syntax.ObjectProperty value;
  
  public InverseObjectProperty (hydra.langs.owl.syntax.ObjectProperty value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof InverseObjectProperty)) {
      return false;
    }
    InverseObjectProperty o = (InverseObjectProperty) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}