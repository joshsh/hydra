package hydra.langs.protobuf.proto3;

import java.io.Serializable;

/**
 * A reference to an enum type or message type
 */
public class TypeReference implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/protobuf/proto3.TypeReference");
  
  /**
   * A reference to an enum type or message type
   */
  public final String value;
  
  public TypeReference (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TypeReference)) {
      return false;
    }
    TypeReference o = (TypeReference) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}