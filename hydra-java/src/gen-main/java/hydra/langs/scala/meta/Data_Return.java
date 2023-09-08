package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_Return implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.Return");
  
  public final hydra.langs.scala.meta.Data expr;
  
  public Data_Return (hydra.langs.scala.meta.Data expr) {
    this.expr = expr;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_Return)) {
      return false;
    }
    Data_Return o = (Data_Return) (other);
    return expr.equals(o.expr);
  }
  
  @Override
  public int hashCode() {
    return 2 * expr.hashCode();
  }
}