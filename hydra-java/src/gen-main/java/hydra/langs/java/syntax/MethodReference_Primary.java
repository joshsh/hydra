package hydra.langs.java.syntax;

import java.io.Serializable;

public class MethodReference_Primary implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.MethodReference.Primary");
  
  public final hydra.langs.java.syntax.Primary primary;
  
  public final java.util.List<hydra.langs.java.syntax.TypeArgument> typeArguments;
  
  public final hydra.langs.java.syntax.Identifier identifier;
  
  public MethodReference_Primary (hydra.langs.java.syntax.Primary primary, java.util.List<hydra.langs.java.syntax.TypeArgument> typeArguments, hydra.langs.java.syntax.Identifier identifier) {
    this.primary = primary;
    this.typeArguments = typeArguments;
    this.identifier = identifier;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof MethodReference_Primary)) {
      return false;
    }
    MethodReference_Primary o = (MethodReference_Primary) (other);
    return primary.equals(o.primary) && typeArguments.equals(o.typeArguments) && identifier.equals(o.identifier);
  }
  
  @Override
  public int hashCode() {
    return 2 * primary.hashCode() + 3 * typeArguments.hashCode() + 5 * identifier.hashCode();
  }
  
  public MethodReference_Primary withPrimary(hydra.langs.java.syntax.Primary primary) {
    return new MethodReference_Primary(primary, typeArguments, identifier);
  }
  
  public MethodReference_Primary withTypeArguments(java.util.List<hydra.langs.java.syntax.TypeArgument> typeArguments) {
    return new MethodReference_Primary(primary, typeArguments, identifier);
  }
  
  public MethodReference_Primary withIdentifier(hydra.langs.java.syntax.Identifier identifier) {
    return new MethodReference_Primary(primary, typeArguments, identifier);
  }
}