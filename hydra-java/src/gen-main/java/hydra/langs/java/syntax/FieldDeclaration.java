package hydra.langs.java.syntax;

import java.io.Serializable;

public class FieldDeclaration implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.FieldDeclaration");
  
  public final java.util.List<hydra.langs.java.syntax.FieldModifier> modifiers;
  
  public final hydra.langs.java.syntax.UnannType unannType;
  
  public final java.util.List<hydra.langs.java.syntax.VariableDeclarator> variableDeclarators;
  
  public FieldDeclaration (java.util.List<hydra.langs.java.syntax.FieldModifier> modifiers, hydra.langs.java.syntax.UnannType unannType, java.util.List<hydra.langs.java.syntax.VariableDeclarator> variableDeclarators) {
    this.modifiers = modifiers;
    this.unannType = unannType;
    this.variableDeclarators = variableDeclarators;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof FieldDeclaration)) {
      return false;
    }
    FieldDeclaration o = (FieldDeclaration) (other);
    return modifiers.equals(o.modifiers) && unannType.equals(o.unannType) && variableDeclarators.equals(o.variableDeclarators);
  }
  
  @Override
  public int hashCode() {
    return 2 * modifiers.hashCode() + 3 * unannType.hashCode() + 5 * variableDeclarators.hashCode();
  }
  
  public FieldDeclaration withModifiers(java.util.List<hydra.langs.java.syntax.FieldModifier> modifiers) {
    return new FieldDeclaration(modifiers, unannType, variableDeclarators);
  }
  
  public FieldDeclaration withUnannType(hydra.langs.java.syntax.UnannType unannType) {
    return new FieldDeclaration(modifiers, unannType, variableDeclarators);
  }
  
  public FieldDeclaration withVariableDeclarators(java.util.List<hydra.langs.java.syntax.VariableDeclarator> variableDeclarators) {
    return new FieldDeclaration(modifiers, unannType, variableDeclarators);
  }
}