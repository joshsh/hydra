package hydra.langs.xml.schema;

import java.io.Serializable;

public class NonPositiveInteger implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.NonPositiveInteger");
  
  public final java.math.BigInteger value;
  
  public NonPositiveInteger (java.math.BigInteger value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof NonPositiveInteger)) {
      return false;
    }
    NonPositiveInteger o = (NonPositiveInteger) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}