package hydra.langs.java.syntax;

import java.io.Serializable;

public class PostDecrementExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.PostDecrementExpression");
  
  public final hydra.langs.java.syntax.PostfixExpression value;
  
  public PostDecrementExpression (hydra.langs.java.syntax.PostfixExpression value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PostDecrementExpression)) {
      return false;
    }
    PostDecrementExpression o = (PostDecrementExpression) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}