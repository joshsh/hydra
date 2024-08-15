// Note: this is an automatically generated file. Do not edit.

package hydra.langs.sql.ansi;

import java.io.Serializable;

public class ContextuallyTypedTableValueConstructor implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/sql/ansi.ContextuallyTypedTableValueConstructor");
  
  public static final hydra.core.Name FIELD_NAME_VALUE = new hydra.core.Name("value");
  
  public final hydra.langs.sql.ansi.ContextuallyTypedRowValueExpressionList value;
  
  public ContextuallyTypedTableValueConstructor (hydra.langs.sql.ansi.ContextuallyTypedRowValueExpressionList value) {
    java.util.Objects.requireNonNull((value));
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ContextuallyTypedTableValueConstructor)) {
      return false;
    }
    ContextuallyTypedTableValueConstructor o = (ContextuallyTypedTableValueConstructor) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}