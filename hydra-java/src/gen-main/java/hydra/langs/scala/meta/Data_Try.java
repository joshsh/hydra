package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_Try implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.Try");
  
  public final hydra.langs.scala.meta.Data expr;
  
  public final java.util.List<hydra.langs.scala.meta.Case> catchp;
  
  public final java.util.Optional<hydra.langs.scala.meta.Data> finallyp;
  
  public Data_Try (hydra.langs.scala.meta.Data expr, java.util.List<hydra.langs.scala.meta.Case> catchp, java.util.Optional<hydra.langs.scala.meta.Data> finallyp) {
    this.expr = expr;
    this.catchp = catchp;
    this.finallyp = finallyp;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_Try)) {
      return false;
    }
    Data_Try o = (Data_Try) (other);
    return expr.equals(o.expr) && catchp.equals(o.catchp) && finallyp.equals(o.finallyp);
  }
  
  @Override
  public int hashCode() {
    return 2 * expr.hashCode() + 3 * catchp.hashCode() + 5 * finallyp.hashCode();
  }
  
  public Data_Try withExpr(hydra.langs.scala.meta.Data expr) {
    return new Data_Try(expr, catchp, finallyp);
  }
  
  public Data_Try withCatchp(java.util.List<hydra.langs.scala.meta.Case> catchp) {
    return new Data_Try(expr, catchp, finallyp);
  }
  
  public Data_Try withFinallyp(java.util.Optional<hydra.langs.scala.meta.Data> finallyp) {
    return new Data_Try(expr, catchp, finallyp);
  }
}