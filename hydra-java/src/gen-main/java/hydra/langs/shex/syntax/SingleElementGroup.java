// Note: this is an automatically generated file. Do not edit.

package hydra.langs.shex.syntax;

import java.io.Serializable;

public class SingleElementGroup implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.SingleElementGroup");
  
  public final hydra.langs.shex.syntax.UnaryTripleExpr unaryTripleExpr;
  
  public final java.util.Optional<java.lang.Void> semi;
  
  public SingleElementGroup (hydra.langs.shex.syntax.UnaryTripleExpr unaryTripleExpr, java.util.Optional<java.lang.Void> semi) {
    if (unaryTripleExpr == null) {
      throw new IllegalArgumentException("null value for 'unaryTripleExpr' argument");
    }
    if (semi == null) {
      throw new IllegalArgumentException("null value for 'semi' argument");
    }
    this.unaryTripleExpr = unaryTripleExpr;
    this.semi = semi;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SingleElementGroup)) {
      return false;
    }
    SingleElementGroup o = (SingleElementGroup) (other);
    return unaryTripleExpr.equals(o.unaryTripleExpr) && semi.equals(o.semi);
  }
  
  @Override
  public int hashCode() {
    return 2 * unaryTripleExpr.hashCode() + 3 * semi.hashCode();
  }
  
  public SingleElementGroup withUnaryTripleExpr(hydra.langs.shex.syntax.UnaryTripleExpr unaryTripleExpr) {
    if (unaryTripleExpr == null) {
      throw new IllegalArgumentException("null value for 'unaryTripleExpr' argument");
    }
    return new SingleElementGroup(unaryTripleExpr, semi);
  }
  
  public SingleElementGroup withSemi(java.util.Optional<java.lang.Void> semi) {
    if (semi == null) {
      throw new IllegalArgumentException("null value for 'semi' argument");
    }
    return new SingleElementGroup(unaryTripleExpr, semi);
  }
}