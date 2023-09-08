package hydra.langs.xml.schema;

import java.io.Serializable;

public class UnsignedByte implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.UnsignedByte");
  
  public final Byte value;
  
  public UnsignedByte (Byte value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof UnsignedByte)) {
      return false;
    }
    UnsignedByte o = (UnsignedByte) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}