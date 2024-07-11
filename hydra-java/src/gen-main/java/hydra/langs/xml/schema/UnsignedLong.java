// Note: this is an automatically generated file. Do not edit.

package hydra.langs.xml.schema;

import java.io.Serializable;

public class UnsignedLong implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.UnsignedLong");
  
  public final java.math.BigInteger value;
  
  public UnsignedLong (java.math.BigInteger value) {
    java.util.Objects.requireNonNull((value));
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof UnsignedLong)) {
      return false;
    }
    UnsignedLong o = (UnsignedLong) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}