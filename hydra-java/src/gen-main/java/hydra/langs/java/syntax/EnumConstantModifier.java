package hydra.langs.java.syntax;

import java.io.Serializable;

public class EnumConstantModifier implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.EnumConstantModifier");
  
  public final hydra.langs.java.syntax.Annotation value;
  
  public EnumConstantModifier (hydra.langs.java.syntax.Annotation value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EnumConstantModifier)) {
      return false;
    }
    EnumConstantModifier o = (EnumConstantModifier) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}