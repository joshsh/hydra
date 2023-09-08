package hydra.langs.haskell.ast;

import java.io.Serializable;

/**
 * A 'let' expression
 */
public class Expression_Let implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.Expression.Let");
  
  public final java.util.List<hydra.langs.haskell.ast.LocalBinding> bindings;
  
  public final hydra.langs.haskell.ast.Expression inner;
  
  public Expression_Let (java.util.List<hydra.langs.haskell.ast.LocalBinding> bindings, hydra.langs.haskell.ast.Expression inner) {
    this.bindings = bindings;
    this.inner = inner;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Expression_Let)) {
      return false;
    }
    Expression_Let o = (Expression_Let) (other);
    return bindings.equals(o.bindings) && inner.equals(o.inner);
  }
  
  @Override
  public int hashCode() {
    return 2 * bindings.hashCode() + 3 * inner.hashCode();
  }
  
  public Expression_Let withBindings(java.util.List<hydra.langs.haskell.ast.LocalBinding> bindings) {
    return new Expression_Let(bindings, inner);
  }
  
  public Expression_Let withInner(hydra.langs.haskell.ast.Expression inner) {
    return new Expression_Let(bindings, inner);
  }
}