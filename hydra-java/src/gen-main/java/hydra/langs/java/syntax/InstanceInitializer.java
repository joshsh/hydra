package hydra.langs.java.syntax;

import java.io.Serializable;

public class InstanceInitializer implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.InstanceInitializer");
  
  public final hydra.langs.java.syntax.Block value;
  
  public InstanceInitializer (hydra.langs.java.syntax.Block value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof InstanceInitializer)) {
      return false;
    }
    InstanceInitializer o = (InstanceInitializer) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}