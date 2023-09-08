package hydra.langs.xml.schema;

import java.io.Serializable;

public class NMTOKEN implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.NMTOKEN");
  
  public final String value;
  
  public NMTOKEN (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof NMTOKEN)) {
      return false;
    }
    NMTOKEN o = (NMTOKEN) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}