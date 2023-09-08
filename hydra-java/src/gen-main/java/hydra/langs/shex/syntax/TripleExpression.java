package hydra.langs.shex.syntax;

import java.io.Serializable;

public class TripleExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.TripleExpression");
  
  public final hydra.langs.shex.syntax.OneOfTripleExpr value;
  
  public TripleExpression (hydra.langs.shex.syntax.OneOfTripleExpr value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TripleExpression)) {
      return false;
    }
    TripleExpression o = (TripleExpression) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}