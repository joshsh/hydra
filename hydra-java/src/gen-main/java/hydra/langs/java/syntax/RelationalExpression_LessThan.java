package hydra.langs.java.syntax;

import java.io.Serializable;

public class RelationalExpression_LessThan implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.RelationalExpression.LessThan");
  
  public final hydra.langs.java.syntax.RelationalExpression lhs;
  
  public final hydra.langs.java.syntax.ShiftExpression rhs;
  
  public RelationalExpression_LessThan (hydra.langs.java.syntax.RelationalExpression lhs, hydra.langs.java.syntax.ShiftExpression rhs) {
    this.lhs = lhs;
    this.rhs = rhs;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof RelationalExpression_LessThan)) {
      return false;
    }
    RelationalExpression_LessThan o = (RelationalExpression_LessThan) (other);
    return lhs.equals(o.lhs) && rhs.equals(o.rhs);
  }
  
  @Override
  public int hashCode() {
    return 2 * lhs.hashCode() + 3 * rhs.hashCode();
  }
  
  public RelationalExpression_LessThan withLhs(hydra.langs.java.syntax.RelationalExpression lhs) {
    return new RelationalExpression_LessThan(lhs, rhs);
  }
  
  public RelationalExpression_LessThan withRhs(hydra.langs.java.syntax.ShiftExpression rhs) {
    return new RelationalExpression_LessThan(lhs, rhs);
  }
}