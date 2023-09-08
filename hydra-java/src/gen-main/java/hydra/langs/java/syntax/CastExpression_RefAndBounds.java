package hydra.langs.java.syntax;

import java.io.Serializable;

public class CastExpression_RefAndBounds implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.CastExpression.RefAndBounds");
  
  public final hydra.langs.java.syntax.ReferenceType type;
  
  public final java.util.List<hydra.langs.java.syntax.AdditionalBound> bounds;
  
  public CastExpression_RefAndBounds (hydra.langs.java.syntax.ReferenceType type, java.util.List<hydra.langs.java.syntax.AdditionalBound> bounds) {
    this.type = type;
    this.bounds = bounds;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof CastExpression_RefAndBounds)) {
      return false;
    }
    CastExpression_RefAndBounds o = (CastExpression_RefAndBounds) (other);
    return type.equals(o.type) && bounds.equals(o.bounds);
  }
  
  @Override
  public int hashCode() {
    return 2 * type.hashCode() + 3 * bounds.hashCode();
  }
  
  public CastExpression_RefAndBounds withType(hydra.langs.java.syntax.ReferenceType type) {
    return new CastExpression_RefAndBounds(type, bounds);
  }
  
  public CastExpression_RefAndBounds withBounds(java.util.List<hydra.langs.java.syntax.AdditionalBound> bounds) {
    return new CastExpression_RefAndBounds(type, bounds);
  }
}