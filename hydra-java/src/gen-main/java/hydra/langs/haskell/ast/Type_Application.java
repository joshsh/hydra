package hydra.langs.haskell.ast;

import java.io.Serializable;

public class Type_Application implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.Type.Application");
  
  public final hydra.langs.haskell.ast.Type context;
  
  public final hydra.langs.haskell.ast.Type argument;
  
  public Type_Application (hydra.langs.haskell.ast.Type context, hydra.langs.haskell.ast.Type argument) {
    this.context = context;
    this.argument = argument;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Type_Application)) {
      return false;
    }
    Type_Application o = (Type_Application) (other);
    return context.equals(o.context) && argument.equals(o.argument);
  }
  
  @Override
  public int hashCode() {
    return 2 * context.hashCode() + 3 * argument.hashCode();
  }
  
  public Type_Application withContext(hydra.langs.haskell.ast.Type context) {
    return new Type_Application(context, argument);
  }
  
  public Type_Application withArgument(hydra.langs.haskell.ast.Type argument) {
    return new Type_Application(context, argument);
  }
}