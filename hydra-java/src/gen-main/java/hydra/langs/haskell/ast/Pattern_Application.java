package hydra.langs.haskell.ast;

import java.io.Serializable;

public class Pattern_Application implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.Pattern.Application");
  
  public final hydra.langs.haskell.ast.Name name;
  
  public final java.util.List<hydra.langs.haskell.ast.Pattern> args;
  
  public Pattern_Application (hydra.langs.haskell.ast.Name name, java.util.List<hydra.langs.haskell.ast.Pattern> args) {
    this.name = name;
    this.args = args;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Pattern_Application)) {
      return false;
    }
    Pattern_Application o = (Pattern_Application) (other);
    return name.equals(o.name) && args.equals(o.args);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * args.hashCode();
  }
  
  public Pattern_Application withName(hydra.langs.haskell.ast.Name name) {
    return new Pattern_Application(name, args);
  }
  
  public Pattern_Application withArgs(java.util.List<hydra.langs.haskell.ast.Pattern> args) {
    return new Pattern_Application(name, args);
  }
}