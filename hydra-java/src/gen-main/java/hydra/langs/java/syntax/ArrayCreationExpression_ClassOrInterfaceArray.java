// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class ArrayCreationExpression_ClassOrInterfaceArray implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ArrayCreationExpression.ClassOrInterfaceArray");
  
  public final hydra.langs.java.syntax.ClassOrInterfaceType type;
  
  public final java.util.List<hydra.langs.java.syntax.Dims> dims;
  
  public final hydra.langs.java.syntax.ArrayInitializer array;
  
  public ArrayCreationExpression_ClassOrInterfaceArray (hydra.langs.java.syntax.ClassOrInterfaceType type, java.util.List<hydra.langs.java.syntax.Dims> dims, hydra.langs.java.syntax.ArrayInitializer array) {
    if (type == null) {
      throw new IllegalArgumentException("null value for 'type' argument");
    }
    if (dims == null) {
      throw new IllegalArgumentException("null value for 'dims' argument");
    }
    if (array == null) {
      throw new IllegalArgumentException("null value for 'array' argument");
    }
    this.type = type;
    this.dims = dims;
    this.array = array;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ArrayCreationExpression_ClassOrInterfaceArray)) {
      return false;
    }
    ArrayCreationExpression_ClassOrInterfaceArray o = (ArrayCreationExpression_ClassOrInterfaceArray) (other);
    return type.equals(o.type) && dims.equals(o.dims) && array.equals(o.array);
  }
  
  @Override
  public int hashCode() {
    return 2 * type.hashCode() + 3 * dims.hashCode() + 5 * array.hashCode();
  }
  
  public ArrayCreationExpression_ClassOrInterfaceArray withType(hydra.langs.java.syntax.ClassOrInterfaceType type) {
    if (type == null) {
      throw new IllegalArgumentException("null value for 'type' argument");
    }
    return new ArrayCreationExpression_ClassOrInterfaceArray(type, dims, array);
  }
  
  public ArrayCreationExpression_ClassOrInterfaceArray withDims(java.util.List<hydra.langs.java.syntax.Dims> dims) {
    if (dims == null) {
      throw new IllegalArgumentException("null value for 'dims' argument");
    }
    return new ArrayCreationExpression_ClassOrInterfaceArray(type, dims, array);
  }
  
  public ArrayCreationExpression_ClassOrInterfaceArray withArray(hydra.langs.java.syntax.ArrayInitializer array) {
    if (array == null) {
      throw new IllegalArgumentException("null value for 'array' argument");
    }
    return new ArrayCreationExpression_ClassOrInterfaceArray(type, dims, array);
  }
}