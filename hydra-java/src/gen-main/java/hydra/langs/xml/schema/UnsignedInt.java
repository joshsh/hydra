package hydra.langs.xml.schema;

import java.io.Serializable;

public class UnsignedInt implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.UnsignedInt");
  
  public final Long value;
  
  public UnsignedInt (Long value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof UnsignedInt)) {
      return false;
    }
    UnsignedInt o = (UnsignedInt) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}