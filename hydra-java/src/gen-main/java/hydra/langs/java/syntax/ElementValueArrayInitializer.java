// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class ElementValueArrayInitializer implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ElementValueArrayInitializer");
  
  public final java.util.List<hydra.langs.java.syntax.ElementValue> value;
  
  public ElementValueArrayInitializer (java.util.List<hydra.langs.java.syntax.ElementValue> value) {
    if (value == null) {
      throw new IllegalArgumentException("null value for 'value' argument");
    }
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ElementValueArrayInitializer)) {
      return false;
    }
    ElementValueArrayInitializer o = (ElementValueArrayInitializer) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}