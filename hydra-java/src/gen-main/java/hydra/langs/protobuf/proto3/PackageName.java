// Note: this is an automatically generated file. Do not edit.

package hydra.langs.protobuf.proto3;

import java.io.Serializable;

public class PackageName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/protobuf/proto3.PackageName");
  
  public final String value;
  
  public PackageName (String value) {
    if (value == null) {
      throw new IllegalArgumentException("null value for 'value' argument");
    }
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PackageName)) {
      return false;
    }
    PackageName o = (PackageName) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}