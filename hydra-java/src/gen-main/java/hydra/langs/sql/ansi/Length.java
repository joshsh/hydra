package hydra.langs.sql.ansi;

import java.io.Serializable;

public class Length implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.Length");
  
  public final hydra.langs.sql.ansi.UnsignedInteger value;
  
  public Length (hydra.langs.sql.ansi.UnsignedInteger value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Length)) {
      return false;
    }
    Length o = (Length) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}