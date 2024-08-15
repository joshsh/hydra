// Note: this is an automatically generated file. Do not edit.

package hydra.langs.sql.ansi;

import java.io.Serializable;

public class ScalarSubquery implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/sql/ansi.ScalarSubquery");
  
  public static final hydra.core.Name FIELD_NAME_VALUE = new hydra.core.Name("value");
  
  public final hydra.langs.sql.ansi.Subquery value;
  
  public ScalarSubquery (hydra.langs.sql.ansi.Subquery value) {
    java.util.Objects.requireNonNull((value));
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ScalarSubquery)) {
      return false;
    }
    ScalarSubquery o = (ScalarSubquery) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}