package hydra.langs.sql.ansi;

import java.io.Serializable;

public class Precision implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.Precision");
  
  public final hydra.langs.sql.ansi.UnsignedInteger value;
  
  public Precision (hydra.langs.sql.ansi.UnsignedInteger value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Precision)) {
      return false;
    }
    Precision o = (Precision) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}