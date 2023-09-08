package hydra.langs.java.syntax;

import java.io.Serializable;

public class PostIncrementExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.PostIncrementExpression");
  
  public final hydra.langs.java.syntax.PostfixExpression value;
  
  public PostIncrementExpression (hydra.langs.java.syntax.PostfixExpression value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PostIncrementExpression)) {
      return false;
    }
    PostIncrementExpression o = (PostIncrementExpression) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}