package hydra.langs.java.syntax;

import java.io.Serializable;

public class CastExpression_Primitive implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.CastExpression.Primitive");
  
  public final hydra.langs.java.syntax.PrimitiveTypeWithAnnotations type;
  
  public final hydra.langs.java.syntax.UnaryExpression expression;
  
  public CastExpression_Primitive (hydra.langs.java.syntax.PrimitiveTypeWithAnnotations type, hydra.langs.java.syntax.UnaryExpression expression) {
    this.type = type;
    this.expression = expression;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof CastExpression_Primitive)) {
      return false;
    }
    CastExpression_Primitive o = (CastExpression_Primitive) (other);
    return type.equals(o.type) && expression.equals(o.expression);
  }
  
  @Override
  public int hashCode() {
    return 2 * type.hashCode() + 3 * expression.hashCode();
  }
  
  public CastExpression_Primitive withType(hydra.langs.java.syntax.PrimitiveTypeWithAnnotations type) {
    return new CastExpression_Primitive(type, expression);
  }
  
  public CastExpression_Primitive withExpression(hydra.langs.java.syntax.UnaryExpression expression) {
    return new CastExpression_Primitive(type, expression);
  }
}