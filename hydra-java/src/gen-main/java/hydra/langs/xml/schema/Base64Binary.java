package hydra.langs.xml.schema;

import java.io.Serializable;

public class Base64Binary implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.Base64Binary");
  
  public final String value;
  
  public Base64Binary (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Base64Binary)) {
      return false;
    }
    Base64Binary o = (Base64Binary) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}