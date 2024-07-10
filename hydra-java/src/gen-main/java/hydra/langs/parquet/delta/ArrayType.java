// Note: this is an automatically generated file. Do not edit.

package hydra.langs.parquet.delta;

import java.io.Serializable;

public class ArrayType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/delta.ArrayType");
  
  public final hydra.langs.parquet.delta.DataType elementType;
  
  public final Boolean containsNull;
  
  public ArrayType (hydra.langs.parquet.delta.DataType elementType, Boolean containsNull) {
    if (elementType == null) {
      throw new IllegalArgumentException("null value for 'elementType' argument");
    }
    if (containsNull == null) {
      throw new IllegalArgumentException("null value for 'containsNull' argument");
    }
    this.elementType = elementType;
    this.containsNull = containsNull;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ArrayType)) {
      return false;
    }
    ArrayType o = (ArrayType) (other);
    return elementType.equals(o.elementType) && containsNull.equals(o.containsNull);
  }
  
  @Override
  public int hashCode() {
    return 2 * elementType.hashCode() + 3 * containsNull.hashCode();
  }
  
  public ArrayType withElementType(hydra.langs.parquet.delta.DataType elementType) {
    if (elementType == null) {
      throw new IllegalArgumentException("null value for 'elementType' argument");
    }
    return new ArrayType(elementType, containsNull);
  }
  
  public ArrayType withContainsNull(Boolean containsNull) {
    if (containsNull == null) {
      throw new IllegalArgumentException("null value for 'containsNull' argument");
    }
    return new ArrayType(elementType, containsNull);
  }
}