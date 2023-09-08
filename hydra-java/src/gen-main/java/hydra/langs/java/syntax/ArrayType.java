package hydra.langs.java.syntax;

import java.io.Serializable;

public class ArrayType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ArrayType");
  
  public final hydra.langs.java.syntax.Dims dims;
  
  public final hydra.langs.java.syntax.ArrayType_Variant variant;
  
  public ArrayType (hydra.langs.java.syntax.Dims dims, hydra.langs.java.syntax.ArrayType_Variant variant) {
    this.dims = dims;
    this.variant = variant;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ArrayType)) {
      return false;
    }
    ArrayType o = (ArrayType) (other);
    return dims.equals(o.dims) && variant.equals(o.variant);
  }
  
  @Override
  public int hashCode() {
    return 2 * dims.hashCode() + 3 * variant.hashCode();
  }
  
  public ArrayType withDims(hydra.langs.java.syntax.Dims dims) {
    return new ArrayType(dims, variant);
  }
  
  public ArrayType withVariant(hydra.langs.java.syntax.ArrayType_Variant variant) {
    return new ArrayType(dims, variant);
  }
}