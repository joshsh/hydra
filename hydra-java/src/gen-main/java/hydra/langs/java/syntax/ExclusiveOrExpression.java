package hydra.langs.java.syntax;

import java.io.Serializable;

public class ExclusiveOrExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ExclusiveOrExpression");
  
  public final java.util.List<hydra.langs.java.syntax.AndExpression> value;
  
  public ExclusiveOrExpression (java.util.List<hydra.langs.java.syntax.AndExpression> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ExclusiveOrExpression)) {
      return false;
    }
    ExclusiveOrExpression o = (ExclusiveOrExpression) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}