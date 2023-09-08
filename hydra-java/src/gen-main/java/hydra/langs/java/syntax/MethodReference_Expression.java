package hydra.langs.java.syntax;

import java.io.Serializable;

public class MethodReference_Expression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.MethodReference.Expression");
  
  public final hydra.langs.java.syntax.ExpressionName name;
  
  public final java.util.List<hydra.langs.java.syntax.TypeArgument> typeArguments;
  
  public final hydra.langs.java.syntax.Identifier identifier;
  
  public MethodReference_Expression (hydra.langs.java.syntax.ExpressionName name, java.util.List<hydra.langs.java.syntax.TypeArgument> typeArguments, hydra.langs.java.syntax.Identifier identifier) {
    this.name = name;
    this.typeArguments = typeArguments;
    this.identifier = identifier;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof MethodReference_Expression)) {
      return false;
    }
    MethodReference_Expression o = (MethodReference_Expression) (other);
    return name.equals(o.name) && typeArguments.equals(o.typeArguments) && identifier.equals(o.identifier);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * typeArguments.hashCode() + 5 * identifier.hashCode();
  }
  
  public MethodReference_Expression withName(hydra.langs.java.syntax.ExpressionName name) {
    return new MethodReference_Expression(name, typeArguments, identifier);
  }
  
  public MethodReference_Expression withTypeArguments(java.util.List<hydra.langs.java.syntax.TypeArgument> typeArguments) {
    return new MethodReference_Expression(name, typeArguments, identifier);
  }
  
  public MethodReference_Expression withIdentifier(hydra.langs.java.syntax.Identifier identifier) {
    return new MethodReference_Expression(name, typeArguments, identifier);
  }
}