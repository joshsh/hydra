package hydra.ext.java.syntax;

public class LocalVariableDeclarationStatement {
  public final LocalVariableDeclaration value;
  
  public LocalVariableDeclarationStatement (LocalVariableDeclaration value) {
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