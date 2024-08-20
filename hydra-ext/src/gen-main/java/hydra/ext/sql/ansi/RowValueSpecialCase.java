// Note: this is an automatically generated file. Do not edit.

package hydra.ext.sql.ansi;

import java.io.Serializable;

public class RowValueSpecialCase implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/ext/sql/ansi.RowValueSpecialCase");
  
  public static final hydra.core.Name FIELD_NAME_VALUE = new hydra.core.Name("value");
  
  public final hydra.ext.sql.ansi.NonparenthesizedValueExpressionPrimary value;
  
  public RowValueSpecialCase (hydra.ext.sql.ansi.NonparenthesizedValueExpressionPrimary value) {
    java.util.Objects.requireNonNull((value));
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof RowValueSpecialCase)) {
      return false;
    }
    RowValueSpecialCase o = (RowValueSpecialCase) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}