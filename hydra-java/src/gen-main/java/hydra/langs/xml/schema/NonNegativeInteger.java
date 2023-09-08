package hydra.langs.xml.schema;

import java.io.Serializable;

public class NonNegativeInteger implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.NonNegativeInteger");
  
  public final java.math.BigInteger value;
  
  public NonNegativeInteger (java.math.BigInteger value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof NonNegativeInteger)) {
      return false;
    }
    NonNegativeInteger o = (NonNegativeInteger) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}