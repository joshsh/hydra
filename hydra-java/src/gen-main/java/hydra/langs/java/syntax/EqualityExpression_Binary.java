// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class EqualityExpression_Binary implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/java/syntax.EqualityExpression.Binary");
  
  public static final hydra.core.Name FIELD_NAME_LHS = new hydra.core.Name("lhs");
  
  public static final hydra.core.Name FIELD_NAME_RHS = new hydra.core.Name("rhs");
  
  public final hydra.langs.java.syntax.EqualityExpression lhs;
  
  public final hydra.langs.java.syntax.RelationalExpression rhs;
  
  public EqualityExpression_Binary (hydra.langs.java.syntax.EqualityExpression lhs, hydra.langs.java.syntax.RelationalExpression rhs) {
    java.util.Objects.requireNonNull((lhs));
    java.util.Objects.requireNonNull((rhs));
    this.lhs = lhs;
    this.rhs = rhs;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EqualityExpression_Binary)) {
      return false;
    }
    EqualityExpression_Binary o = (EqualityExpression_Binary) (other);
    return lhs.equals(o.lhs) && rhs.equals(o.rhs);
  }
  
  @Override
  public int hashCode() {
    return 2 * lhs.hashCode() + 3 * rhs.hashCode();
  }
  
  public EqualityExpression_Binary withLhs(hydra.langs.java.syntax.EqualityExpression lhs) {
    java.util.Objects.requireNonNull((lhs));
    return new EqualityExpression_Binary(lhs, rhs);
  }
  
  public EqualityExpression_Binary withRhs(hydra.langs.java.syntax.RelationalExpression rhs) {
    java.util.Objects.requireNonNull((rhs));
    return new EqualityExpression_Binary(lhs, rhs);
  }
}