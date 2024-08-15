// Note: this is an automatically generated file. Do not edit.

package hydra.langs.cypher.openCypher;

import java.io.Serializable;

public class Unwind implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/cypher/openCypher.Unwind");
  
  public static final hydra.core.Name FIELD_NAME_EXPRESSION = new hydra.core.Name("expression");
  
  public static final hydra.core.Name FIELD_NAME_VARIABLE = new hydra.core.Name("variable");
  
  public final hydra.langs.cypher.openCypher.Expression expression;
  
  public final hydra.langs.cypher.openCypher.Variable variable;
  
  public Unwind (hydra.langs.cypher.openCypher.Expression expression, hydra.langs.cypher.openCypher.Variable variable) {
    java.util.Objects.requireNonNull((expression));
    java.util.Objects.requireNonNull((variable));
    this.expression = expression;
    this.variable = variable;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Unwind)) {
      return false;
    }
    Unwind o = (Unwind) (other);
    return expression.equals(o.expression) && variable.equals(o.variable);
  }
  
  @Override
  public int hashCode() {
    return 2 * expression.hashCode() + 3 * variable.hashCode();
  }
  
  public Unwind withExpression(hydra.langs.cypher.openCypher.Expression expression) {
    java.util.Objects.requireNonNull((expression));
    return new Unwind(expression, variable);
  }
  
  public Unwind withVariable(hydra.langs.cypher.openCypher.Variable variable) {
    java.util.Objects.requireNonNull((variable));
    return new Unwind(expression, variable);
  }
}