package hydra.langs.java.syntax;

import java.io.Serializable;

public class PreIncrementExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.PreIncrementExpression");
  
  public final hydra.langs.java.syntax.UnaryExpression value;
  
  public PreIncrementExpression (hydra.langs.java.syntax.UnaryExpression value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PreIncrementExpression)) {
      return false;
    }
    PreIncrementExpression o = (PreIncrementExpression) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}