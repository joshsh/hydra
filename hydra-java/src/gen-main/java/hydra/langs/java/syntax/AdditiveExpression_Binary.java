package hydra.langs.java.syntax;

import java.io.Serializable;

public class AdditiveExpression_Binary implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.AdditiveExpression.Binary");
  
  public final hydra.langs.java.syntax.AdditiveExpression lhs;
  
  public final hydra.langs.java.syntax.MultiplicativeExpression rhs;
  
  public AdditiveExpression_Binary (hydra.langs.java.syntax.AdditiveExpression lhs, hydra.langs.java.syntax.MultiplicativeExpression rhs) {
    this.lhs = lhs;
    this.rhs = rhs;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof AdditiveExpression_Binary)) {
      return false;
    }
    AdditiveExpression_Binary o = (AdditiveExpression_Binary) (other);
    return lhs.equals(o.lhs) && rhs.equals(o.rhs);
  }
  
  @Override
  public int hashCode() {
    return 2 * lhs.hashCode() + 3 * rhs.hashCode();
  }
  
  public AdditiveExpression_Binary withLhs(hydra.langs.java.syntax.AdditiveExpression lhs) {
    return new AdditiveExpression_Binary(lhs, rhs);
  }
  
  public AdditiveExpression_Binary withRhs(hydra.langs.java.syntax.MultiplicativeExpression rhs) {
    return new AdditiveExpression_Binary(lhs, rhs);
  }
}