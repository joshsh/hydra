// Note: this is an automatically generated file. Do not edit.

package hydra.langs.cypher.openCypher;

import java.io.Serializable;

public class MultiplyDivideModuloExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/cypher/openCypher.MultiplyDivideModuloExpression");
  
  public final hydra.langs.cypher.openCypher.PowerOfExpression left;
  
  public final java.util.List<hydra.langs.cypher.openCypher.MultiplyDivideModuloRightHandSide> right;
  
  public MultiplyDivideModuloExpression (hydra.langs.cypher.openCypher.PowerOfExpression left, java.util.List<hydra.langs.cypher.openCypher.MultiplyDivideModuloRightHandSide> right) {
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
    if (!(other instanceof MultiplyDivideModuloExpression)) {
      return false;
    }
    MultiplyDivideModuloExpression o = (MultiplyDivideModuloExpression) (other);
    return left.equals(o.left) && right.equals(o.right);
  }
  
  @Override
  public int hashCode() {
    return 2 * left.hashCode() + 3 * right.hashCode();
  }
  
  public MultiplyDivideModuloExpression withLeft(hydra.langs.cypher.openCypher.PowerOfExpression left) {
    if (left == null) {
      throw new IllegalArgumentException("null value for 'left' argument");
    }
    return new MultiplyDivideModuloExpression(left, right);
  }
  
  public MultiplyDivideModuloExpression withRight(java.util.List<hydra.langs.cypher.openCypher.MultiplyDivideModuloRightHandSide> right) {
    if (right == null) {
      throw new IllegalArgumentException("null value for 'right' argument");
    }
    return new MultiplyDivideModuloExpression(left, right);
  }
}