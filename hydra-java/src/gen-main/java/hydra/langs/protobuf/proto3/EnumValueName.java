package hydra.langs.protobuf.proto3;

import java.io.Serializable;

public class EnumValueName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/protobuf/proto3.EnumValueName");
  
  public final String value;
  
  public EnumValueName (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EnumValueName)) {
      return false;
    }
    EnumValueName o = (EnumValueName) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}