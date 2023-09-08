package hydra.langs.xml.schema;

import java.io.Serializable;

public class GYearMonth implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.GYearMonth");
  
  public final String value;
  
  public GYearMonth (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof GYearMonth)) {
      return false;
    }
    GYearMonth o = (GYearMonth) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}