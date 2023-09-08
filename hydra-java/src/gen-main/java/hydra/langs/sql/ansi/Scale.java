package hydra.langs.sql.ansi;

import java.io.Serializable;

public class Scale implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.Scale");
  
  public final hydra.langs.sql.ansi.UnsignedInteger value;
  
  public Scale (hydra.langs.sql.ansi.UnsignedInteger value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Scale)) {
      return false;
    }
    Scale o = (Scale) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}