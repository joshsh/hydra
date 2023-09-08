package hydra.langs.sql.ansi;

import java.io.Serializable;

public class UnsignedInteger implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.UnsignedInteger");
  
  public final String value;
  
  public UnsignedInteger (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof UnsignedInteger)) {
      return false;
    }
    UnsignedInteger o = (UnsignedInteger) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}