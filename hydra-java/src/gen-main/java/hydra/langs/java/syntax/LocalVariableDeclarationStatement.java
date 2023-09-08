package hydra.langs.java.syntax;

import java.io.Serializable;

public class LocalVariableDeclarationStatement implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.LocalVariableDeclarationStatement");
  
  public final hydra.langs.java.syntax.LocalVariableDeclaration value;
  
  public LocalVariableDeclarationStatement (hydra.langs.java.syntax.LocalVariableDeclaration value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof LocalVariableDeclarationStatement)) {
      return false;
    }
    LocalVariableDeclarationStatement o = (LocalVariableDeclarationStatement) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}