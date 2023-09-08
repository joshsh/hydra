package hydra.langs.xml.schema;

import java.io.Serializable;

public class IDREF implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.IDREF");
  
  public final String value;
  
  public IDREF (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof IDREF)) {
      return false;
    }
    IDREF o = (IDREF) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}