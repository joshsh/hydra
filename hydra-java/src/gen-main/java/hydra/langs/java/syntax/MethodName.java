package hydra.langs.java.syntax;

import java.io.Serializable;

public class MethodName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.MethodName");
  
  public final hydra.langs.java.syntax.Identifier value;
  
  public MethodName (hydra.langs.java.syntax.Identifier value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof MethodName)) {
      return false;
    }
    MethodName o = (MethodName) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}