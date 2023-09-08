package hydra.langs.haskell.ast;

import java.io.Serializable;

public class Type_Infix implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.Type.Infix");
  
  public final hydra.langs.haskell.ast.Type lhs;
  
  public final hydra.langs.haskell.ast.Operator operator;
  
  public final hydra.langs.haskell.ast.Operator rhs;
  
  public Type_Infix (hydra.langs.haskell.ast.Type lhs, hydra.langs.haskell.ast.Operator operator, hydra.langs.haskell.ast.Operator rhs) {
    this.lhs = lhs;
    this.operator = operator;
    this.rhs = rhs;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Type_Infix)) {
      return false;
    }
    Type_Infix o = (Type_Infix) (other);
    return lhs.equals(o.lhs) && operator.equals(o.operator) && rhs.equals(o.rhs);
  }
  
  @Override
  public int hashCode() {
    return 2 * lhs.hashCode() + 3 * operator.hashCode() + 5 * rhs.hashCode();
  }
  
  public Type_Infix withLhs(hydra.langs.haskell.ast.Type lhs) {
    return new Type_Infix(lhs, operator, rhs);
  }
  
  public Type_Infix withOperator(hydra.langs.haskell.ast.Operator operator) {
    return new Type_Infix(lhs, operator, rhs);
  }
  
  public Type_Infix withRhs(hydra.langs.haskell.ast.Operator rhs) {
    return new Type_Infix(lhs, operator, rhs);
  }
}