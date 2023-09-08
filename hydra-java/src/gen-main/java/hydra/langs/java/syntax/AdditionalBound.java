package hydra.langs.java.syntax;

import java.io.Serializable;

public class AdditionalBound implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.AdditionalBound");
  
  public final hydra.langs.java.syntax.InterfaceType value;
  
  public AdditionalBound (hydra.langs.java.syntax.InterfaceType value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof AdditionalBound)) {
      return false;
    }
    AdditionalBound o = (AdditionalBound) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}