package hydra.langs.java.syntax;

import java.io.Serializable;

/**
 * A ClassType which does not allow annotations
 */
public class UnannClassType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.UnannClassType");
  
  /**
   * A ClassType which does not allow annotations
   */
  public final hydra.langs.java.syntax.ClassType value;
  
  public UnannClassType (hydra.langs.java.syntax.ClassType value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof UnannClassType)) {
      return false;
    }
    UnannClassType o = (UnannClassType) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}