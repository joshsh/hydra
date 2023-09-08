package hydra.langs.haskell.ast;

import java.io.Serializable;

public class Type_Context implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.Type.Context");
  
  public final hydra.langs.haskell.ast.Assertion ctx;
  
  public final hydra.langs.haskell.ast.Type type;
  
  public Type_Context (hydra.langs.haskell.ast.Assertion ctx, hydra.langs.haskell.ast.Type type) {
    this.ctx = ctx;
    this.type = type;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Type_Context)) {
      return false;
    }
    Type_Context o = (Type_Context) (other);
    return ctx.equals(o.ctx) && type.equals(o.type);
  }
  
  @Override
  public int hashCode() {
    return 2 * ctx.hashCode() + 3 * type.hashCode();
  }
  
  public Type_Context withCtx(hydra.langs.haskell.ast.Assertion ctx) {
    return new Type_Context(ctx, type);
  }
  
  public Type_Context withType(hydra.langs.haskell.ast.Type type) {
    return new Type_Context(ctx, type);
  }
}