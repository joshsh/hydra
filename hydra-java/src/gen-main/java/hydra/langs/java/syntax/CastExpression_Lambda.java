package hydra.langs.java.syntax;

import java.io.Serializable;

public class CastExpression_Lambda implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.CastExpression.Lambda");
  
  public final hydra.langs.java.syntax.CastExpression_RefAndBounds refAndBounds;
  
  public final hydra.langs.java.syntax.LambdaExpression expression;
  
  public CastExpression_Lambda (hydra.langs.java.syntax.CastExpression_RefAndBounds refAndBounds, hydra.langs.java.syntax.LambdaExpression expression) {
    this.refAndBounds = refAndBounds;
    this.expression = expression;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof CastExpression_Lambda)) {
      return false;
    }
    CastExpression_Lambda o = (CastExpression_Lambda) (other);
    return refAndBounds.equals(o.refAndBounds) && expression.equals(o.expression);
  }
  
  @Override
  public int hashCode() {
    return 2 * refAndBounds.hashCode() + 3 * expression.hashCode();
  }
  
  public CastExpression_Lambda withRefAndBounds(hydra.langs.java.syntax.CastExpression_RefAndBounds refAndBounds) {
    return new CastExpression_Lambda(refAndBounds, expression);
  }
  
  public CastExpression_Lambda withExpression(hydra.langs.java.syntax.LambdaExpression expression) {
    return new CastExpression_Lambda(refAndBounds, expression);
  }
}