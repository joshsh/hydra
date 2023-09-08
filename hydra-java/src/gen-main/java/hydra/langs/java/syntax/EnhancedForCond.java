package hydra.langs.java.syntax;

import java.io.Serializable;

public class EnhancedForCond implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.EnhancedForCond");
  
  public final java.util.List<hydra.langs.java.syntax.VariableModifier> modifiers;
  
  public final hydra.langs.java.syntax.LocalVariableType type;
  
  public final hydra.langs.java.syntax.VariableDeclaratorId id;
  
  public final hydra.langs.java.syntax.Expression expression;
  
  public EnhancedForCond (java.util.List<hydra.langs.java.syntax.VariableModifier> modifiers, hydra.langs.java.syntax.LocalVariableType type, hydra.langs.java.syntax.VariableDeclaratorId id, hydra.langs.java.syntax.Expression expression) {
    this.modifiers = modifiers;
    this.type = type;
    this.id = id;
    this.expression = expression;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EnhancedForCond)) {
      return false;
    }
    EnhancedForCond o = (EnhancedForCond) (other);
    return modifiers.equals(o.modifiers) && type.equals(o.type) && id.equals(o.id) && expression.equals(o.expression);
  }
  
  @Override
  public int hashCode() {
    return 2 * modifiers.hashCode() + 3 * type.hashCode() + 5 * id.hashCode() + 7 * expression.hashCode();
  }
  
  public EnhancedForCond withModifiers(java.util.List<hydra.langs.java.syntax.VariableModifier> modifiers) {
    return new EnhancedForCond(modifiers, type, id, expression);
  }
  
  public EnhancedForCond withType(hydra.langs.java.syntax.LocalVariableType type) {
    return new EnhancedForCond(modifiers, type, id, expression);
  }
  
  public EnhancedForCond withId(hydra.langs.java.syntax.VariableDeclaratorId id) {
    return new EnhancedForCond(modifiers, type, id, expression);
  }
  
  public EnhancedForCond withExpression(hydra.langs.java.syntax.Expression expression) {
    return new EnhancedForCond(modifiers, type, id, expression);
  }
}