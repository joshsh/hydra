package hydra.langs.protobuf.proto3;

import java.io.Serializable;

/**
 * The local name of an enum type or message type
 */
public class TypeName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/protobuf/proto3.TypeName");
  
  /**
   * The local name of an enum type or message type
   */
  public final String value;
  
  public TypeName (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TypeName)) {
      return false;
    }
    TypeName o = (TypeName) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}