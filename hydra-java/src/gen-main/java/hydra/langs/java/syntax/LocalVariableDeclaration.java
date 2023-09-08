package hydra.langs.java.syntax;

import java.io.Serializable;

public class LocalVariableDeclaration implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.LocalVariableDeclaration");
  
  public final java.util.List<hydra.langs.java.syntax.VariableModifier> modifiers;
  
  public final hydra.langs.java.syntax.LocalVariableType type;
  
  public final java.util.List<hydra.langs.java.syntax.VariableDeclarator> declarators;
  
  public LocalVariableDeclaration (java.util.List<hydra.langs.java.syntax.VariableModifier> modifiers, hydra.langs.java.syntax.LocalVariableType type, java.util.List<hydra.langs.java.syntax.VariableDeclarator> declarators) {
    this.modifiers = modifiers;
    this.type = type;
    this.declarators = declarators;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof LocalVariableDeclaration)) {
      return false;
    }
    LocalVariableDeclaration o = (LocalVariableDeclaration) (other);
    return modifiers.equals(o.modifiers) && type.equals(o.type) && declarators.equals(o.declarators);
  }
  
  @Override
  public int hashCode() {
    return 2 * modifiers.hashCode() + 3 * type.hashCode() + 5 * declarators.hashCode();
  }
  
  public LocalVariableDeclaration withModifiers(java.util.List<hydra.langs.java.syntax.VariableModifier> modifiers) {
    return new LocalVariableDeclaration(modifiers, type, declarators);
  }
  
  public LocalVariableDeclaration withType(hydra.langs.java.syntax.LocalVariableType type) {
    return new LocalVariableDeclaration(modifiers, type, declarators);
  }
  
  public LocalVariableDeclaration withDeclarators(java.util.List<hydra.langs.java.syntax.VariableDeclarator> declarators) {
    return new LocalVariableDeclaration(modifiers, type, declarators);
  }
}