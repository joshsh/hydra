// Note: this is an automatically generated file. Do not edit.

package hydra.langs.sql.ansi;

import java.io.Serializable;

public class RowValueSpecialCase implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.RowValueSpecialCase");
  
  public final hydra.langs.sql.ansi.NonparenthesizedValueExpressionPrimary value;
  
  public RowValueSpecialCase (hydra.langs.sql.ansi.NonparenthesizedValueExpressionPrimary value) {
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