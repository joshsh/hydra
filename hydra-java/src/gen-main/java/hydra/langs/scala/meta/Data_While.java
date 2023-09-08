package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_While implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.While");
  
  public final hydra.langs.scala.meta.Data expr;
  
  public final hydra.langs.scala.meta.Data body;
  
  public Data_While (hydra.langs.scala.meta.Data expr, hydra.langs.scala.meta.Data body) {
    this.expr = expr;
    this.body = body;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_While)) {
      return false;
    }
    Data_While o = (Data_While) (other);
    return expr.equals(o.expr) && body.equals(o.body);
  }
  
  @Override
  public int hashCode() {
    return 2 * expr.hashCode() + 3 * body.hashCode();
  }
  
  public Data_While withExpr(hydra.langs.scala.meta.Data expr) {
    return new Data_While(expr, body);
  }
  
  public Data_While withBody(hydra.langs.scala.meta.Data body) {
    return new Data_While(expr, body);
  }
}