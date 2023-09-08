package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_Throw implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.Throw");
  
  public final hydra.langs.scala.meta.Data expr;
  
  public Data_Throw (hydra.langs.scala.meta.Data expr) {
    this.expr = expr;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_Throw)) {
      return false;
    }
    Data_Throw o = (Data_Throw) (other);
    return expr.equals(o.expr);
  }
  
  @Override
  public int hashCode() {
    return 2 * expr.hashCode();
  }
}