package hydra.langs.java.syntax;

import java.io.Serializable;

public class EnumBody implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.EnumBody");
  
  public final java.util.List<hydra.langs.java.syntax.EnumBody_Element> value;
  
  public EnumBody (java.util.List<hydra.langs.java.syntax.EnumBody_Element> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EnumBody)) {
      return false;
    }
    EnumBody o = (EnumBody) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}