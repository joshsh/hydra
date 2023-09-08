package hydra.langs.xml.schema;

import java.io.Serializable;

public class GYear implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.GYear");
  
  public final String value;
  
  public GYear (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof GYear)) {
      return false;
    }
    GYear o = (GYear) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}