package hydra.langs.haskell.ast;

import java.io.Serializable;

/**
 * A prefix expression
 */
public class Expression_PrefixApplication implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.Expression.PrefixApplication");
  
  public final hydra.langs.haskell.ast.Operator operator;
  
  public final hydra.langs.haskell.ast.Expression rhs;
  
  public Expression_PrefixApplication (hydra.langs.haskell.ast.Operator operator, hydra.langs.haskell.ast.Expression rhs) {
    this.operator = operator;
    this.rhs = rhs;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Expression_PrefixApplication)) {
      return false;
    }
    Expression_PrefixApplication o = (Expression_PrefixApplication) (other);
    return operator.equals(o.operator) && rhs.equals(o.rhs);
  }
  
  @Override
  public int hashCode() {
    return 2 * operator.hashCode() + 3 * rhs.hashCode();
  }
  
  public Expression_PrefixApplication withOperator(hydra.langs.haskell.ast.Operator operator) {
    return new Expression_PrefixApplication(operator, rhs);
  }
  
  public Expression_PrefixApplication withRhs(hydra.langs.haskell.ast.Expression rhs) {
    return new Expression_PrefixApplication(operator, rhs);
  }
}