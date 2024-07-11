// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class ArrayCreationExpression_ClassOrInterface implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ArrayCreationExpression.ClassOrInterface");
  
  public final hydra.langs.java.syntax.ClassOrInterfaceType type;
  
  public final java.util.List<hydra.langs.java.syntax.DimExpr> dimExprs;
  
  public final hydra.util.Opt<hydra.langs.java.syntax.Dims> dims;
  
  public ArrayCreationExpression_ClassOrInterface (hydra.langs.java.syntax.ClassOrInterfaceType type, java.util.List<hydra.langs.java.syntax.DimExpr> dimExprs, hydra.util.Opt<hydra.langs.java.syntax.Dims> dims) {
    java.util.Objects.requireNonNull((type));
    java.util.Objects.requireNonNull((dimExprs));
    java.util.Objects.requireNonNull((dims));
    this.type = type;
    this.dimExprs = dimExprs;
    this.dims = dims;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ArrayCreationExpression_ClassOrInterface)) {
      return false;
    }
    ArrayCreationExpression_ClassOrInterface o = (ArrayCreationExpression_ClassOrInterface) (other);
    return type.equals(o.type) && dimExprs.equals(o.dimExprs) && dims.equals(o.dims);
  }
  
  @Override
  public int hashCode() {
    return 2 * type.hashCode() + 3 * dimExprs.hashCode() + 5 * dims.hashCode();
  }
  
  public ArrayCreationExpression_ClassOrInterface withType(hydra.langs.java.syntax.ClassOrInterfaceType type) {
    java.util.Objects.requireNonNull((type));
    return new ArrayCreationExpression_ClassOrInterface(type, dimExprs, dims);
  }
  
  public ArrayCreationExpression_ClassOrInterface withDimExprs(java.util.List<hydra.langs.java.syntax.DimExpr> dimExprs) {
    java.util.Objects.requireNonNull((dimExprs));
    return new ArrayCreationExpression_ClassOrInterface(type, dimExprs, dims);
  }
  
  public ArrayCreationExpression_ClassOrInterface withDims(hydra.util.Opt<hydra.langs.java.syntax.Dims> dims) {
    java.util.Objects.requireNonNull((dims));
    return new ArrayCreationExpression_ClassOrInterface(type, dimExprs, dims);
  }
}