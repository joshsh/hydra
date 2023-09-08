package hydra.langs.haskell.ast;

import java.io.Serializable;

/**
 * A 'deriving' statement
 */
public class Deriving implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.Deriving");
  
  /**
   * A 'deriving' statement
   */
  public final java.util.List<hydra.langs.haskell.ast.Name> value;
  
  public Deriving (java.util.List<hydra.langs.haskell.ast.Name> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Deriving)) {
      return false;
    }
    Deriving o = (Deriving) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}