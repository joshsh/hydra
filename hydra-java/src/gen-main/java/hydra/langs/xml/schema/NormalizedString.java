package hydra.langs.xml.schema;

import java.io.Serializable;

public class NormalizedString implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.NormalizedString");
  
  public final String value;
  
  public NormalizedString (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof NormalizedString)) {
      return false;
    }
    NormalizedString o = (NormalizedString) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}