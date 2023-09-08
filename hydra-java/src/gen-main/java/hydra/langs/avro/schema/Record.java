package hydra.langs.avro.schema;

import java.io.Serializable;

public class Record implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/avro/schema.Record");
  
  /**
   * a JSON array, listing fields
   */
  public final java.util.List<hydra.langs.avro.schema.Field> fields;
  
  public Record (java.util.List<hydra.langs.avro.schema.Field> fields) {
    this.fields = fields;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Record)) {
      return false;
    }
    Record o = (Record) (other);
    return fields.equals(o.fields);
  }
  
  @Override
  public int hashCode() {
    return 2 * fields.hashCode();
  }
}