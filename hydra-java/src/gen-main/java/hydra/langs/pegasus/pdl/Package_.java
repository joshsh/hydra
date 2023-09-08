package hydra.langs.pegasus.pdl;

import java.io.Serializable;

public class Package_ implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/pegasus/pdl.Package");
  
  public final String value;
  
  public Package_ (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Package_)) {
      return false;
    }
    Package_ o = (Package_) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}