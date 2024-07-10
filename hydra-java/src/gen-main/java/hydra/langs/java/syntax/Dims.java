// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class Dims implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.Dims");
  
  public final java.util.List<java.util.List<hydra.langs.java.syntax.Annotation>> value;
  
  public Dims (java.util.List<java.util.List<hydra.langs.java.syntax.Annotation>> value) {
    if (value == null) {
      throw new IllegalArgumentException("null value for 'value' argument");
    }
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Dims)) {
      return false;
    }
    Dims o = (Dims) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}