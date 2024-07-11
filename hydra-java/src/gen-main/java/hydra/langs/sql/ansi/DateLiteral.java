// Note: this is an automatically generated file. Do not edit.

package hydra.langs.sql.ansi;

import java.io.Serializable;

public class DateLiteral implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.DateLiteral");
  
  public final hydra.langs.sql.ansi.DateString value;
  
  public DateLiteral (hydra.langs.sql.ansi.DateString value) {
    java.util.Objects.requireNonNull((value));
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DateLiteral)) {
      return false;
    }
    DateLiteral o = (DateLiteral) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}