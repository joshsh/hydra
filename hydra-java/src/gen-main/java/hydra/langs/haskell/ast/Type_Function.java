package hydra.langs.haskell.ast;

import java.io.Serializable;

public class Type_Function implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.Type.Function");
  
  public final hydra.langs.haskell.ast.Type domain;
  
  public final hydra.langs.haskell.ast.Type codomain;
  
  public Type_Function (hydra.langs.haskell.ast.Type domain, hydra.langs.haskell.ast.Type codomain) {
    this.domain = domain;
    this.codomain = codomain;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Type_Function)) {
      return false;
    }
    Type_Function o = (Type_Function) (other);
    return domain.equals(o.domain) && codomain.equals(o.codomain);
  }
  
  @Override
  public int hashCode() {
    return 2 * domain.hashCode() + 3 * codomain.hashCode();
  }
  
  public Type_Function withDomain(hydra.langs.haskell.ast.Type domain) {
    return new Type_Function(domain, codomain);
  }
  
  public Type_Function withCodomain(hydra.langs.haskell.ast.Type codomain) {
    return new Type_Function(domain, codomain);
  }
}