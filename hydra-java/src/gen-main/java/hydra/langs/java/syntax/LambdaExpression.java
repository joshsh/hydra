// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class LambdaExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.LambdaExpression");
  
  public final hydra.langs.java.syntax.LambdaParameters parameters;
  
  public final hydra.langs.java.syntax.LambdaBody body;
  
  public LambdaExpression (hydra.langs.java.syntax.LambdaParameters parameters, hydra.langs.java.syntax.LambdaBody body) {
    if (parameters == null) {
      throw new IllegalArgumentException("null value for 'parameters' argument");
    }
    if (body == null) {
      throw new IllegalArgumentException("null value for 'body' argument");
    }
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
    if (parameters == null) {
      throw new IllegalArgumentException("null value for 'parameters' argument");
    }
    return new LambdaExpression(parameters, body);
  }
  
  public LambdaExpression withBody(hydra.langs.java.syntax.LambdaBody body) {
    if (body == null) {
      throw new IllegalArgumentException("null value for 'body' argument");
    }
    return new LambdaExpression(parameters, body);
  }
}