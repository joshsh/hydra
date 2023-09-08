package hydra.langs.haskell.ast;

import java.io.Serializable;

/**
 * An infix application expression
 */
public class Expression_InfixApplication implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.Expression.InfixApplication");
  
  public final hydra.langs.haskell.ast.Expression lhs;
  
  public final hydra.langs.haskell.ast.Operator operator;
  
  public final hydra.langs.haskell.ast.Expression rhs;
  
  public Expression_InfixApplication (hydra.langs.haskell.ast.Expression lhs, hydra.langs.haskell.ast.Operator operator, hydra.langs.haskell.ast.Expression rhs) {
    this.lhs = lhs;
    this.operator = operator;
    this.rhs = rhs;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Expression_InfixApplication)) {
      return false;
    }
    Expression_InfixApplication o = (Expression_InfixApplication) (other);
    return lhs.equals(o.lhs) && operator.equals(o.operator) && rhs.equals(o.rhs);
  }
  
  @Override
  public int hashCode() {
    return 2 * lhs.hashCode() + 3 * operator.hashCode() + 5 * rhs.hashCode();
  }
  
  public Expression_InfixApplication withLhs(hydra.langs.haskell.ast.Expression lhs) {
    return new Expression_InfixApplication(lhs, operator, rhs);
  }
  
  public Expression_InfixApplication withOperator(hydra.langs.haskell.ast.Operator operator) {
    return new Expression_InfixApplication(lhs, operator, rhs);
  }
  
  public Expression_InfixApplication withRhs(hydra.langs.haskell.ast.Expression rhs) {
    return new Expression_InfixApplication(lhs, operator, rhs);
  }
}