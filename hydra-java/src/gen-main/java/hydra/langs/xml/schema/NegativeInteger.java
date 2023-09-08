package hydra.langs.xml.schema;

import java.io.Serializable;

public class NegativeInteger implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.NegativeInteger");
  
  public final java.math.BigInteger value;
  
  public NegativeInteger (java.math.BigInteger value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof NegativeInteger)) {
      return false;
    }
    NegativeInteger o = (NegativeInteger) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}