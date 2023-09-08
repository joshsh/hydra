package hydra.langs.haskell.ast;

import java.io.Serializable;

public class Assertion_Class implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.Assertion.Class");
  
  public final hydra.langs.haskell.ast.Name name;
  
  public final java.util.List<hydra.langs.haskell.ast.Type> types;
  
  public Assertion_Class (hydra.langs.haskell.ast.Name name, java.util.List<hydra.langs.haskell.ast.Type> types) {
    this.name = name;
    this.types = types;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Assertion_Class)) {
      return false;
    }
    Assertion_Class o = (Assertion_Class) (other);
    return name.equals(o.name) && types.equals(o.types);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * types.hashCode();
  }
  
  public Assertion_Class withName(hydra.langs.haskell.ast.Name name) {
    return new Assertion_Class(name, types);
  }
  
  public Assertion_Class withTypes(java.util.List<hydra.langs.haskell.ast.Type> types) {
    return new Assertion_Class(name, types);
  }
}