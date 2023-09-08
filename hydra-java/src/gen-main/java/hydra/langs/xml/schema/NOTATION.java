package hydra.langs.xml.schema;

import java.io.Serializable;

public class NOTATION implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.NOTATION");
  
  public final String value;
  
  public NOTATION (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof NOTATION)) {
      return false;
    }
    NOTATION o = (NOTATION) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}