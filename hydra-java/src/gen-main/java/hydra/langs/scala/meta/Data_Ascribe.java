package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_Ascribe implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.Ascribe");
  
  public final hydra.langs.scala.meta.Data expr;
  
  public final hydra.langs.scala.meta.Type tpe;
  
  public Data_Ascribe (hydra.langs.scala.meta.Data expr, hydra.langs.scala.meta.Type tpe) {
    this.expr = expr;
    this.tpe = tpe;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_Ascribe)) {
      return false;
    }
    Data_Ascribe o = (Data_Ascribe) (other);
    return expr.equals(o.expr) && tpe.equals(o.tpe);
  }
  
  @Override
  public int hashCode() {
    return 2 * expr.hashCode() + 3 * tpe.hashCode();
  }
  
  public Data_Ascribe withExpr(hydra.langs.scala.meta.Data expr) {
    return new Data_Ascribe(expr, tpe);
  }
  
  public Data_Ascribe withTpe(hydra.langs.scala.meta.Type tpe) {
    return new Data_Ascribe(expr, tpe);
  }
}