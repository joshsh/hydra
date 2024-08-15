// Note: this is an automatically generated file. Do not edit.

package hydra.langs.tinkerpop.gremlin;

import java.io.Serializable;

public class IntegerRange implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/tinkerpop/gremlin.IntegerRange");
  
  public static final hydra.core.Name FIELD_NAME_LEFT = new hydra.core.Name("left");
  
  public static final hydra.core.Name FIELD_NAME_RIGHT = new hydra.core.Name("right");
  
  public final hydra.langs.tinkerpop.gremlin.IntegerLiteral left;
  
  public final hydra.langs.tinkerpop.gremlin.IntegerLiteral right;
  
  public IntegerRange (hydra.langs.tinkerpop.gremlin.IntegerLiteral left, hydra.langs.tinkerpop.gremlin.IntegerLiteral right) {
    java.util.Objects.requireNonNull((left));
    java.util.Objects.requireNonNull((right));
    this.left = left;
    this.right = right;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof IntegerRange)) {
      return false;
    }
    IntegerRange o = (IntegerRange) (other);
    return left.equals(o.left) && right.equals(o.right);
  }
  
  @Override
  public int hashCode() {
    return 2 * left.hashCode() + 3 * right.hashCode();
  }
  
  public IntegerRange withLeft(hydra.langs.tinkerpop.gremlin.IntegerLiteral left) {
    java.util.Objects.requireNonNull((left));
    return new IntegerRange(left, right);
  }
  
  public IntegerRange withRight(hydra.langs.tinkerpop.gremlin.IntegerLiteral right) {
    java.util.Objects.requireNonNull((right));
    return new IntegerRange(left, right);
  }
}