package hydra.langs.java.syntax;

import java.io.Serializable;

public class ConditionalAndExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ConditionalAndExpression");
  
  public final java.util.List<hydra.langs.java.syntax.InclusiveOrExpression> value;
  
  public ConditionalAndExpression (java.util.List<hydra.langs.java.syntax.InclusiveOrExpression> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ConditionalAndExpression)) {
      return false;
    }
    ConditionalAndExpression o = (ConditionalAndExpression) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}