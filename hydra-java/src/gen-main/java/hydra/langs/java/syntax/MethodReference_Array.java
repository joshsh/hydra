package hydra.langs.java.syntax;

import java.io.Serializable;

public class MethodReference_Array implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.MethodReference.Array");
  
  public final hydra.langs.java.syntax.ArrayType value;
  
  public MethodReference_Array (hydra.langs.java.syntax.ArrayType value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof MethodReference_Array)) {
      return false;
    }
    MethodReference_Array o = (MethodReference_Array) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}