package hydra.langs.xml.schema;

import java.io.Serializable;

public class Long_ implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.Long");
  
  public final Long value;
  
  public Long_ (Long value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Long_)) {
      return false;
    }
    Long_ o = (Long_) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}