package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_Match implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.Match");
  
  public final hydra.langs.scala.meta.Data expr;
  
  public final java.util.List<hydra.langs.scala.meta.Case> cases;
  
  public Data_Match (hydra.langs.scala.meta.Data expr, java.util.List<hydra.langs.scala.meta.Case> cases) {
    this.expr = expr;
    this.cases = cases;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_Match)) {
      return false;
    }
    Data_Match o = (Data_Match) (other);
    return expr.equals(o.expr) && cases.equals(o.cases);
  }
  
  @Override
  public int hashCode() {
    return 2 * expr.hashCode() + 3 * cases.hashCode();
  }
  
  public Data_Match withExpr(hydra.langs.scala.meta.Data expr) {
    return new Data_Match(expr, cases);
  }
  
  public Data_Match withCases(java.util.List<hydra.langs.scala.meta.Case> cases) {
    return new Data_Match(expr, cases);
  }
}