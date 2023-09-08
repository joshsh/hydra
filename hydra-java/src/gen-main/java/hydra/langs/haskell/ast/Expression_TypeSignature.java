package hydra.langs.haskell.ast;

import java.io.Serializable;

/**
 * A type signature expression
 */
public class Expression_TypeSignature implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.Expression.TypeSignature");
  
  public final hydra.langs.haskell.ast.Expression inner;
  
  public final hydra.langs.haskell.ast.Type type;
  
  public Expression_TypeSignature (hydra.langs.haskell.ast.Expression inner, hydra.langs.haskell.ast.Type type) {
    this.inner = inner;
    this.type = type;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Expression_TypeSignature)) {
      return false;
    }
    Expression_TypeSignature o = (Expression_TypeSignature) (other);
    return inner.equals(o.inner) && type.equals(o.type);
  }
  
  @Override
  public int hashCode() {
    return 2 * inner.hashCode() + 3 * type.hashCode();
  }
  
  public Expression_TypeSignature withInner(hydra.langs.haskell.ast.Expression inner) {
    return new Expression_TypeSignature(inner, type);
  }
  
  public Expression_TypeSignature withType(hydra.langs.haskell.ast.Type type) {
    return new Expression_TypeSignature(inner, type);
  }
}