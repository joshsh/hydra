package hydra.langs.haskell.ast;

import java.io.Serializable;

public class LocalBindings implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.LocalBindings");
  
  public final java.util.List<hydra.langs.haskell.ast.LocalBinding> value;
  
  public LocalBindings (java.util.List<hydra.langs.haskell.ast.LocalBinding> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof LocalBindings)) {
      return false;
    }
    LocalBindings o = (LocalBindings) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}