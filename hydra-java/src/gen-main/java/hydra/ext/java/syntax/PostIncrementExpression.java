package hydra.ext.java.syntax;

public class PostIncrementExpression {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/java/syntax.PostIncrementExpression");
  
  public final hydra.ext.java.syntax.PostfixExpression value;
  
  public PostIncrementExpression (hydra.ext.java.syntax.PostfixExpression value) {
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