package hydra.langs.java.syntax;

import java.io.Serializable;

public class ConditionalOrExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ConditionalOrExpression");
  
  public final java.util.List<hydra.langs.java.syntax.ConditionalAndExpression> value;
  
  public ConditionalOrExpression (java.util.List<hydra.langs.java.syntax.ConditionalAndExpression> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ConditionalOrExpression)) {
      return false;
    }
    ConditionalOrExpression o = (ConditionalOrExpression) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}