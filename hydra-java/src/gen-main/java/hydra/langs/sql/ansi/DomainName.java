package hydra.langs.sql.ansi;

import java.io.Serializable;

public class DomainName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.DomainName");
  
  public final String value;
  
  public DomainName (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DomainName)) {
      return false;
    }
    DomainName o = (DomainName) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}