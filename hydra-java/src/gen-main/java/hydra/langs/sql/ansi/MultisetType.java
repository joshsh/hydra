package hydra.langs.sql.ansi;

import java.io.Serializable;

public class MultisetType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.MultisetType");
  
  public final hydra.langs.sql.ansi.DataType value;
  
  public MultisetType (hydra.langs.sql.ansi.DataType value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof MultisetType)) {
      return false;
    }
    MultisetType o = (MultisetType) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}