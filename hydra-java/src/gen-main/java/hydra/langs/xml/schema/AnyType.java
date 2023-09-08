package hydra.langs.xml.schema;

import java.io.Serializable;

public class AnyType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.AnyType");
  
  public final String value;
  
  public AnyType (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof AnyType)) {
      return false;
    }
    AnyType o = (AnyType) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}