package hydra.langs.xml.schema;

import java.io.Serializable;

public class UnsignedShort implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.UnsignedShort");
  
  public final Character value;
  
  public UnsignedShort (Character value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof UnsignedShort)) {
      return false;
    }
    UnsignedShort o = (UnsignedShort) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}