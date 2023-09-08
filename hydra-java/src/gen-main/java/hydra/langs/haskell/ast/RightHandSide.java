package hydra.langs.haskell.ast;

import java.io.Serializable;

public class RightHandSide implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.RightHandSide");
  
  public final hydra.langs.haskell.ast.Expression value;
  
  public RightHandSide (hydra.langs.haskell.ast.Expression value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof RightHandSide)) {
      return false;
    }
    RightHandSide o = (RightHandSide) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}