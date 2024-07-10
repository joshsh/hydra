// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class ShiftExpression_Binary implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ShiftExpression.Binary");
  
  public final hydra.langs.java.syntax.ShiftExpression lhs;
  
  public final hydra.langs.java.syntax.AdditiveExpression rhs;
  
  public ShiftExpression_Binary (hydra.langs.java.syntax.ShiftExpression lhs, hydra.langs.java.syntax.AdditiveExpression rhs) {
    if (lhs == null) {
      throw new IllegalArgumentException("null value for 'lhs' argument");
    }
    if (rhs == null) {
      throw new IllegalArgumentException("null value for 'rhs' argument");
    }
    this.lhs = lhs;
    this.rhs = rhs;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ShiftExpression_Binary)) {
      return false;
    }
    ShiftExpression_Binary o = (ShiftExpression_Binary) (other);
    return lhs.equals(o.lhs) && rhs.equals(o.rhs);
  }
  
  @Override
  public int hashCode() {
    return 2 * lhs.hashCode() + 3 * rhs.hashCode();
  }
  
  public ShiftExpression_Binary withLhs(hydra.langs.java.syntax.ShiftExpression lhs) {
    if (lhs == null) {
      throw new IllegalArgumentException("null value for 'lhs' argument");
    }
    return new ShiftExpression_Binary(lhs, rhs);
  }
  
  public ShiftExpression_Binary withRhs(hydra.langs.java.syntax.AdditiveExpression rhs) {
    if (rhs == null) {
      throw new IllegalArgumentException("null value for 'rhs' argument");
    }
    return new ShiftExpression_Binary(lhs, rhs);
  }
}