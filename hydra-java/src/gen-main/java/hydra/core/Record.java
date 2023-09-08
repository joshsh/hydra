package hydra.core;

import java.io.Serializable;

/**
 * A record, or labeled tuple; a map of field names to terms
 */
public class Record<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/core.Record");
  
  public final hydra.core.Name typeName;
  
  public final java.util.List<hydra.core.Field<A>> fields;
  
  public Record (hydra.core.Name typeName, java.util.List<hydra.core.Field<A>> fields) {
    this.typeName = typeName;
    this.fields = fields;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Record)) {
      return false;
    }
    Record o = (Record) (other);
    return typeName.equals(o.typeName) && fields.equals(o.fields);
  }
  
  @Override
  public int hashCode() {
    return 2 * typeName.hashCode() + 3 * fields.hashCode();
  }
  
  public Record withTypeName(hydra.core.Name typeName) {
    return new Record(typeName, fields);
  }
  
  public Record withFields(java.util.List<hydra.core.Field<A>> fields) {
    return new Record(typeName, fields);
  }
}