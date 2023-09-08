package hydra.langs.avro.schema;

import java.io.Serializable;

public class Map implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/avro/schema.Map");
  
  public final hydra.langs.avro.schema.Schema values;
  
  public Map (hydra.langs.avro.schema.Schema values) {
    this.values = values;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Map)) {
      return false;
    }
    Map o = (Map) (other);
    return values.equals(o.values);
  }
  
  @Override
  public int hashCode() {
    return 2 * values.hashCode();
  }
}