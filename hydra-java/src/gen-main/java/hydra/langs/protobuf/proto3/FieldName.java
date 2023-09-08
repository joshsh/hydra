package hydra.langs.protobuf.proto3;

import java.io.Serializable;

/**
 * The name of a field
 */
public class FieldName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/protobuf/proto3.FieldName");
  
  /**
   * The name of a field
   */
  public final String value;
  
  public FieldName (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof FieldName)) {
      return false;
    }
    FieldName o = (FieldName) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}