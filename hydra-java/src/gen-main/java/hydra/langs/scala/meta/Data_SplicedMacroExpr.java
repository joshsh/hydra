// Note: this is an automatically generated file. Do not edit.

package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_SplicedMacroExpr implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.SplicedMacroExpr");
  
  public static final hydra.core.Name FIELD_NAME_BODY = new hydra.core.Name("body");
  
  public final hydra.langs.scala.meta.Data body;
  
  public Data_SplicedMacroExpr (hydra.langs.scala.meta.Data body) {
    java.util.Objects.requireNonNull((body));
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