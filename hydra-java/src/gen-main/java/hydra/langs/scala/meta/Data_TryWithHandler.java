package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_TryWithHandler implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.TryWithHandler");
  
  public final hydra.langs.scala.meta.Data expr;
  
  public final hydra.langs.scala.meta.Data catchp;
  
  public final java.util.Optional<hydra.langs.scala.meta.Data> finallyp;
  
  public Data_TryWithHandler (hydra.langs.scala.meta.Data expr, hydra.langs.scala.meta.Data catchp, java.util.Optional<hydra.langs.scala.meta.Data> finallyp) {
    this.expr = expr;
    this.catchp = catchp;
    this.finallyp = finallyp;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_TryWithHandler)) {
      return false;
    }
    Data_TryWithHandler o = (Data_TryWithHandler) (other);
    return expr.equals(o.expr) && catchp.equals(o.catchp) && finallyp.equals(o.finallyp);
  }
  
  @Override
  public int hashCode() {
    return 2 * expr.hashCode() + 3 * catchp.hashCode() + 5 * finallyp.hashCode();
  }
  
  public Data_TryWithHandler withExpr(hydra.langs.scala.meta.Data expr) {
    return new Data_TryWithHandler(expr, catchp, finallyp);
  }
  
  public Data_TryWithHandler withCatchp(hydra.langs.scala.meta.Data catchp) {
    return new Data_TryWithHandler(expr, catchp, finallyp);
  }
  
  public Data_TryWithHandler withFinallyp(java.util.Optional<hydra.langs.scala.meta.Data> finallyp) {
    return new Data_TryWithHandler(expr, catchp, finallyp);
  }
}