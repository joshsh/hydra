package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_ContextFunction implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.ContextFunction");
  
  public final java.util.List<hydra.langs.scala.meta.Data_Param> params;
  
  public final hydra.langs.scala.meta.Data body;
  
  public Data_ContextFunction (java.util.List<hydra.langs.scala.meta.Data_Param> params, hydra.langs.scala.meta.Data body) {
    this.params = params;
    this.body = body;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_ContextFunction)) {
      return false;
    }
    Data_ContextFunction o = (Data_ContextFunction) (other);
    return params.equals(o.params) && body.equals(o.body);
  }
  
  @Override
  public int hashCode() {
    return 2 * params.hashCode() + 3 * body.hashCode();
  }
  
  public Data_ContextFunction withParams(java.util.List<hydra.langs.scala.meta.Data_Param> params) {
    return new Data_ContextFunction(params, body);
  }
  
  public Data_ContextFunction withBody(hydra.langs.scala.meta.Data body) {
    return new Data_ContextFunction(params, body);
  }
}