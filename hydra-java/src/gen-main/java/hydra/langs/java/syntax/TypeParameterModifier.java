// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class TypeParameterModifier implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/java/syntax.TypeParameterModifier");
  
  public static final hydra.core.Name FIELD_NAME_VALUE = new hydra.core.Name("value");
  
  public final hydra.langs.java.syntax.Annotation value;
  
  public TypeParameterModifier (hydra.langs.java.syntax.Annotation value) {
    java.util.Objects.requireNonNull((value));
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TypeParameterModifier)) {
      return false;
    }
    TypeParameterModifier o = (TypeParameterModifier) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}