package hydra.langs.java.syntax;

import java.io.Serializable;

public class ConstantDeclaration implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ConstantDeclaration");
  
  public final java.util.List<hydra.langs.java.syntax.ConstantModifier> modifiers;
  
  public final hydra.langs.java.syntax.UnannType type;
  
  public final java.util.List<hydra.langs.java.syntax.VariableDeclarator> variables;
  
  public ConstantDeclaration (java.util.List<hydra.langs.java.syntax.ConstantModifier> modifiers, hydra.langs.java.syntax.UnannType type, java.util.List<hydra.langs.java.syntax.VariableDeclarator> variables) {
    this.modifiers = modifiers;
    this.type = type;
    this.variables = variables;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ConstantDeclaration)) {
      return false;
    }
    ConstantDeclaration o = (ConstantDeclaration) (other);
    return modifiers.equals(o.modifiers) && type.equals(o.type) && variables.equals(o.variables);
  }
  
  @Override
  public int hashCode() {
    return 2 * modifiers.hashCode() + 3 * type.hashCode() + 5 * variables.hashCode();
  }
  
  public ConstantDeclaration withModifiers(java.util.List<hydra.langs.java.syntax.ConstantModifier> modifiers) {
    return new ConstantDeclaration(modifiers, type, variables);
  }
  
  public ConstantDeclaration withType(hydra.langs.java.syntax.UnannType type) {
    return new ConstantDeclaration(modifiers, type, variables);
  }
  
  public ConstantDeclaration withVariables(java.util.List<hydra.langs.java.syntax.VariableDeclarator> variables) {
    return new ConstantDeclaration(modifiers, type, variables);
  }
}