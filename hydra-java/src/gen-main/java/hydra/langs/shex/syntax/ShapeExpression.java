package hydra.langs.shex.syntax;

import java.io.Serializable;

public class ShapeExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.ShapeExpression");
  
  public final hydra.langs.shex.syntax.ShapeOr value;
  
  public ShapeExpression (hydra.langs.shex.syntax.ShapeOr value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ShapeExpression)) {
      return false;
    }
    ShapeExpression o = (ShapeExpression) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}