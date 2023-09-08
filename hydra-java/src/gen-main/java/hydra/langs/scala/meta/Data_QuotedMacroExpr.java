package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_QuotedMacroExpr implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.QuotedMacroExpr");
  
  public final hydra.langs.scala.meta.Data body;
  
  public Data_QuotedMacroExpr (hydra.langs.scala.meta.Data body) {
    this.body = body;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_QuotedMacroExpr)) {
      return false;
    }
    Data_QuotedMacroExpr o = (Data_QuotedMacroExpr) (other);
    return body.equals(o.body);
  }
  
  @Override
  public int hashCode() {
    return 2 * body.hashCode();
  }
}