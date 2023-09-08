package hydra.langs.java.syntax;

import java.io.Serializable;

public class Resource_Local implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.Resource.Local");
  
  public final java.util.List<hydra.langs.java.syntax.VariableModifier> modifiers;
  
  public final hydra.langs.java.syntax.LocalVariableType type;
  
  public final hydra.langs.java.syntax.Identifier identifier;
  
  public final hydra.langs.java.syntax.Expression expression;
  
  public Resource_Local (java.util.List<hydra.langs.java.syntax.VariableModifier> modifiers, hydra.langs.java.syntax.LocalVariableType type, hydra.langs.java.syntax.Identifier identifier, hydra.langs.java.syntax.Expression expression) {
    this.modifiers = modifiers;
    this.type = type;
    this.identifier = identifier;
    this.expression = expression;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Resource_Local)) {
      return false;
    }
    Resource_Local o = (Resource_Local) (other);
    return modifiers.equals(o.modifiers) && type.equals(o.type) && identifier.equals(o.identifier) && expression.equals(o.expression);
  }
  
  @Override
  public int hashCode() {
    return 2 * modifiers.hashCode() + 3 * type.hashCode() + 5 * identifier.hashCode() + 7 * expression.hashCode();
  }
  
  public Resource_Local withModifiers(java.util.List<hydra.langs.java.syntax.VariableModifier> modifiers) {
    return new Resource_Local(modifiers, type, identifier, expression);
  }
  
  public Resource_Local withType(hydra.langs.java.syntax.LocalVariableType type) {
    return new Resource_Local(modifiers, type, identifier, expression);
  }
  
  public Resource_Local withIdentifier(hydra.langs.java.syntax.Identifier identifier) {
    return new Resource_Local(modifiers, type, identifier, expression);
  }
  
  public Resource_Local withExpression(hydra.langs.java.syntax.Expression expression) {
    return new Resource_Local(modifiers, type, identifier, expression);
  }
}