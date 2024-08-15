// Note: this is an automatically generated file. Do not edit.

package hydra.langs.kusto.kql;

import java.io.Serializable;

public class LetBinding implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/kusto/kql.LetBinding");
  
  public static final hydra.core.Name FIELD_NAME_NAME = new hydra.core.Name("name");
  
  public static final hydra.core.Name FIELD_NAME_EXPRESSION = new hydra.core.Name("expression");
  
  public final hydra.langs.kusto.kql.ColumnName name;
  
  public final hydra.langs.kusto.kql.Expression expression;
  
  public LetBinding (hydra.langs.kusto.kql.ColumnName name, hydra.langs.kusto.kql.Expression expression) {
    java.util.Objects.requireNonNull((name));
    java.util.Objects.requireNonNull((expression));
    this.name = name;
    this.expression = expression;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof LetBinding)) {
      return false;
    }
    LetBinding o = (LetBinding) (other);
    return name.equals(o.name) && expression.equals(o.expression);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * expression.hashCode();
  }
  
  public LetBinding withName(hydra.langs.kusto.kql.ColumnName name) {
    java.util.Objects.requireNonNull((name));
    return new LetBinding(name, expression);
  }
  
  public LetBinding withExpression(hydra.langs.kusto.kql.Expression expression) {
    java.util.Objects.requireNonNull((expression));
    return new LetBinding(name, expression);
  }
}