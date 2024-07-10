// Note: this is an automatically generated file. Do not edit.

package hydra.langs.cypher.openCypher;

import java.io.Serializable;

public class AddOrSubtractRightHandSide implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/cypher/openCypher.AddOrSubtractRightHandSide");
  
  public final hydra.langs.cypher.openCypher.AddOrSubtractOperator operator;
  
  public final hydra.langs.cypher.openCypher.MultiplyDivideModuloExpression expression;
  
  public AddOrSubtractRightHandSide (hydra.langs.cypher.openCypher.AddOrSubtractOperator operator, hydra.langs.cypher.openCypher.MultiplyDivideModuloExpression expression) {
    if (operator == null) {
      throw new IllegalArgumentException("null value for 'operator' argument");
    }
    if (expression == null) {
      throw new IllegalArgumentException("null value for 'expression' argument");
    }
    this.operator = operator;
    this.expression = expression;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof AddOrSubtractRightHandSide)) {
      return false;
    }
    AddOrSubtractRightHandSide o = (AddOrSubtractRightHandSide) (other);
    return operator.equals(o.operator) && expression.equals(o.expression);
  }
  
  @Override
  public int hashCode() {
    return 2 * operator.hashCode() + 3 * expression.hashCode();
  }
  
  public AddOrSubtractRightHandSide withOperator(hydra.langs.cypher.openCypher.AddOrSubtractOperator operator) {
    if (operator == null) {
      throw new IllegalArgumentException("null value for 'operator' argument");
    }
    return new AddOrSubtractRightHandSide(operator, expression);
  }
  
  public AddOrSubtractRightHandSide withExpression(hydra.langs.cypher.openCypher.MultiplyDivideModuloExpression expression) {
    if (expression == null) {
      throw new IllegalArgumentException("null value for 'expression' argument");
    }
    return new AddOrSubtractRightHandSide(operator, expression);
  }
}