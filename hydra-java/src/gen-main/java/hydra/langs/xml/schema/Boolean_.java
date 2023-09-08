package hydra.langs.xml.schema;

import java.io.Serializable;

public class Boolean_ implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.Boolean");
  
  public final Boolean value;
  
  public Boolean_ (Boolean value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Boolean_)) {
      return false;
    }
    Boolean_ o = (Boolean_) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}