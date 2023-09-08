package hydra.langs.xml.schema;

import java.io.Serializable;

public class ENTITIES implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.ENTITIES");
  
  public final String value;
  
  public ENTITIES (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ENTITIES)) {
      return false;
    }
    ENTITIES o = (ENTITIES) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}