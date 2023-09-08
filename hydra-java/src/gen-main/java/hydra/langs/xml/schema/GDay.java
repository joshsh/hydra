package hydra.langs.xml.schema;

import java.io.Serializable;

public class GDay implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.GDay");
  
  public final String value;
  
  public GDay (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof GDay)) {
      return false;
    }
    GDay o = (GDay) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}