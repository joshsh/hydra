package hydra.langs.java.syntax;

import java.io.Serializable;

public class TypeParameterModifier implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.TypeParameterModifier");
  
  public final hydra.langs.java.syntax.Annotation value;
  
  public TypeParameterModifier (hydra.langs.java.syntax.Annotation value) {
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