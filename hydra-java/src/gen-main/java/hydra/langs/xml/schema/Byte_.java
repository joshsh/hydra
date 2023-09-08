package hydra.langs.xml.schema;

import java.io.Serializable;

public class Byte_ implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.Byte");
  
  public final Short value;
  
  public Byte_ (Short value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Byte_)) {
      return false;
    }
    Byte_ o = (Byte_) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}