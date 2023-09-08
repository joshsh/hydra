package hydra.langs.shex.syntax;

import java.io.Serializable;

public class InlineShapeExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.InlineShapeExpression");
  
  public final hydra.langs.shex.syntax.InlineShapeOr value;
  
  public InlineShapeExpression (hydra.langs.shex.syntax.InlineShapeOr value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof InlineShapeExpression)) {
      return false;
    }
    InlineShapeExpression o = (InlineShapeExpression) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}