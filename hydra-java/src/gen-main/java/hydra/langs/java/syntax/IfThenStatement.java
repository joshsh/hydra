// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class IfThenStatement implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.IfThenStatement");
  
  public final hydra.langs.java.syntax.Expression expression;
  
  public final hydra.langs.java.syntax.Statement statement;
  
  public IfThenStatement (hydra.langs.java.syntax.Expression expression, hydra.langs.java.syntax.Statement statement) {
    if (expression == null) {
      throw new IllegalArgumentException("null value for 'expression' argument");
    }
    if (statement == null) {
      throw new IllegalArgumentException("null value for 'statement' argument");
    }
    this.expression = expression;
    this.statement = statement;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof IfThenStatement)) {
      return false;
    }
    IfThenStatement o = (IfThenStatement) (other);
    return expression.equals(o.expression) && statement.equals(o.statement);
  }
  
  @Override
  public int hashCode() {
    return 2 * expression.hashCode() + 3 * statement.hashCode();
  }
  
  public IfThenStatement withExpression(hydra.langs.java.syntax.Expression expression) {
    if (expression == null) {
      throw new IllegalArgumentException("null value for 'expression' argument");
    }
    return new IfThenStatement(expression, statement);
  }
  
  public IfThenStatement withStatement(hydra.langs.java.syntax.Statement statement) {
    if (statement == null) {
      throw new IllegalArgumentException("null value for 'statement' argument");
    }
    return new IfThenStatement(expression, statement);
  }
}