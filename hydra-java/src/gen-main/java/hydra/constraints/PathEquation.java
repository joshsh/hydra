package hydra.constraints;

import java.io.Serializable;

/**
 * A declared equivalence between two abstract paths in a graph
 */
public class PathEquation implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/constraints.PathEquation");
  
  public final hydra.query.Path left;
  
  public final hydra.query.Path right;
  
  public PathEquation (hydra.query.Path left, hydra.query.Path right) {
    this.left = left;
    this.right = right;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PathEquation)) {
      return false;
    }
    PathEquation o = (PathEquation) (other);
    return left.equals(o.left) && right.equals(o.right);
  }
  
  @Override
  public int hashCode() {
    return 2 * left.hashCode() + 3 * right.hashCode();
  }
  
  public PathEquation withLeft(hydra.query.Path left) {
    return new PathEquation(left, right);
  }
  
  public PathEquation withRight(hydra.query.Path right) {
    return new PathEquation(left, right);
  }
}