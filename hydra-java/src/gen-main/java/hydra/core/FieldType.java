// Note: this is an automatically generated file. Do not edit.

package hydra.core;

import java.io.Serializable;

/**
 * The name and type of a field
 */
public class FieldType<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/core.FieldType");
  
  public final hydra.core.FieldName name;
  
  public final hydra.core.Type<A> type;
  
  public FieldType (hydra.core.FieldName name, hydra.core.Type<A> type) {
    if (name == null) {
      throw new IllegalArgumentException("null value for 'name' argument");
    }
    if (type == null) {
      throw new IllegalArgumentException("null value for 'type' argument");
    }
    this.name = name;
    this.type = type;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof FieldType)) {
      return false;
    }
    FieldType o = (FieldType) (other);
    return name.equals(o.name) && type.equals(o.type);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * type.hashCode();
  }
  
  public FieldType withName(hydra.core.FieldName name) {
    if (name == null) {
      throw new IllegalArgumentException("null value for 'name' argument");
    }
    return new FieldType(name, type);
  }
  
  public FieldType withType(hydra.core.Type<A> type) {
    if (type == null) {
      throw new IllegalArgumentException("null value for 'type' argument");
    }
    return new FieldType(name, type);
  }
}