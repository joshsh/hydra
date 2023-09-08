package hydra.langs.java.syntax;

import java.io.Serializable;

public class LambdaExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.LambdaExpression");
  
  public final hydra.langs.java.syntax.LambdaParameters parameters;
  
  public final hydra.langs.java.syntax.LambdaBody body;
  
  public LambdaExpression (hydra.langs.java.syntax.LambdaParameters parameters, hydra.langs.java.syntax.LambdaBody body) {
    this.parameters = parameters;
    this.body = body;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof LambdaExpression)) {
      return false;
    }
    LambdaExpression o = (LambdaExpression) (other);
    return parameters.equals(o.parameters) && body.equals(o.body);
  }
  
  @Override
  public int hashCode() {
    return 2 * parameters.hashCode() + 3 * body.hashCode();
  }
  
  public LambdaExpression withParameters(hydra.langs.java.syntax.LambdaParameters parameters) {
    return new LambdaExpression(parameters, body);
  }
  
  public LambdaExpression withBody(hydra.langs.java.syntax.LambdaBody body) {
    return new LambdaExpression(parameters, body);
  }
}