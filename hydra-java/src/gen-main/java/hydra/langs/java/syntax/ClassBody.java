package hydra.langs.java.syntax;

import java.io.Serializable;

public class ClassBody implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ClassBody");
  
  public final java.util.List<hydra.langs.java.syntax.ClassBodyDeclarationWithComments> value;
  
  public ClassBody (java.util.List<hydra.langs.java.syntax.ClassBodyDeclarationWithComments> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ClassBody)) {
      return false;
    }
    ClassBody o = (ClassBody) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}