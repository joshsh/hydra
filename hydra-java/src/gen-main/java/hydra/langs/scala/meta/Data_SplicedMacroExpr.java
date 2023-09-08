package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_SplicedMacroExpr implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.SplicedMacroExpr");
  
  public final hydra.langs.scala.meta.Data body;
  
  public Data_SplicedMacroExpr (hydra.langs.scala.meta.Data body) {
    this.body = body;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_SplicedMacroExpr)) {
      return false;
    }
    Data_SplicedMacroExpr o = (Data_SplicedMacroExpr) (other);
    return body.equals(o.body);
  }
  
  @Override
  public int hashCode() {
    return 2 * body.hashCode();
  }
}