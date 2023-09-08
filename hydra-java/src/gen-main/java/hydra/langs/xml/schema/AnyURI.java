package hydra.langs.xml.schema;

import java.io.Serializable;

public class AnyURI implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.AnyURI");
  
  public final String value;
  
  public AnyURI (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof AnyURI)) {
      return false;
    }
    AnyURI o = (AnyURI) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}