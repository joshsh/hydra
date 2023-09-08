package hydra.langs.xml.schema;

import java.io.Serializable;

public class Short_ implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.Short");
  
  public final Short value;
  
  public Short_ (Short value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Short_)) {
      return false;
    }
    Short_ o = (Short_) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}