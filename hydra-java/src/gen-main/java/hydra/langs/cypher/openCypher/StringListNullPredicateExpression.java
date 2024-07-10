// Note: this is an automatically generated file. Do not edit.

package hydra.langs.cypher.openCypher;

import java.io.Serializable;

public class StringListNullPredicateExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/cypher/openCypher.StringListNullPredicateExpression");
  
  public final hydra.langs.cypher.openCypher.AddOrSubtractExpression left;
  
  public final java.util.List<hydra.langs.cypher.openCypher.StringListNullPredicateRightHandSide> right;
  
  public StringListNullPredicateExpression (hydra.langs.cypher.openCypher.AddOrSubtractExpression left, java.util.List<hydra.langs.cypher.openCypher.StringListNullPredicateRightHandSide> right) {
    if (left == null) {
      throw new IllegalArgumentException("null value for 'left' argument");
    }
    if (right == null) {
      throw new IllegalArgumentException("null value for 'right' argument");
    }
    this.left = left;
    this.right = right;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof StringListNullPredicateExpression)) {
      return false;
    }
    StringListNullPredicateExpression o = (StringListNullPredicateExpression) (other);
    return left.equals(o.left) && right.equals(o.right);
  }
  
  @Override
  public int hashCode() {
    return 2 * left.hashCode() + 3 * right.hashCode();
  }
  
  public StringListNullPredicateExpression withLeft(hydra.langs.cypher.openCypher.AddOrSubtractExpression left) {
    if (left == null) {
      throw new IllegalArgumentException("null value for 'left' argument");
    }
    return new StringListNullPredicateExpression(left, right);
  }
  
  public StringListNullPredicateExpression withRight(java.util.List<hydra.langs.cypher.openCypher.StringListNullPredicateRightHandSide> right) {
    if (right == null) {
      throw new IllegalArgumentException("null value for 'right' argument");
    }
    return new StringListNullPredicateExpression(left, right);
  }
}