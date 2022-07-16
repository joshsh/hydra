package hydra.ext.java.syntax;

public class EnhancedForCond {
  public final java.util.List<VariableModifier> modifiers;
  
  public final LocalVariableType type;
  
  public final VariableDeclaratorId id;
  
  public final Expression expression;
  
  public EnhancedForCond (java.util.List<VariableModifier> modifiers, LocalVariableType type, VariableDeclaratorId id, Expression expression) {
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
  
  public EnhancedForCond withModifiers(java.util.List<VariableModifier> modifiers) {
    return new EnhancedForCond(modifiers, type, id, expression);
  }
  
  public EnhancedForCond withType(LocalVariableType type) {
    return new EnhancedForCond(modifiers, type, id, expression);
  }
  
  public EnhancedForCond withId(VariableDeclaratorId id) {
    return new EnhancedForCond(modifiers, type, id, expression);
  }
  
  public EnhancedForCond withExpression(Expression expression) {
    return new EnhancedForCond(modifiers, type, id, expression);
  }
}