package hydra.langs.haskell.ast;

import java.io.Serializable;

public class Pattern_As implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.Pattern.As");
  
  public final hydra.langs.haskell.ast.Name name;
  
  public final hydra.langs.haskell.ast.Pattern inner;
  
  public Pattern_As (hydra.langs.haskell.ast.Name name, hydra.langs.haskell.ast.Pattern inner) {
    this.name = name;
    this.inner = inner;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Pattern_As)) {
      return false;
    }
    Pattern_As o = (Pattern_As) (other);
    return name.equals(o.name) && inner.equals(o.inner);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * inner.hashCode();
  }
  
  public Pattern_As withName(hydra.langs.haskell.ast.Name name) {
    return new Pattern_As(name, inner);
  }
  
  public Pattern_As withInner(hydra.langs.haskell.ast.Pattern inner) {
    return new Pattern_As(name, inner);
  }
}