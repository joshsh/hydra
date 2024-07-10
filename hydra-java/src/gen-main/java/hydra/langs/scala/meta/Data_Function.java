// Note: this is an automatically generated file. Do not edit.

package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_Function implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.Function");
  
  public final java.util.List<hydra.langs.scala.meta.Data_Param> params;
  
  public final hydra.langs.scala.meta.Data body;
  
  public Data_Function (java.util.List<hydra.langs.scala.meta.Data_Param> params, hydra.langs.scala.meta.Data body) {
    if (params == null) {
      throw new IllegalArgumentException("null value for 'params' argument");
    }
    if (body == null) {
      throw new IllegalArgumentException("null value for 'body' argument");
    }
    this.params = params;
    this.body = body;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_Function)) {
      return false;
    }
    Data_Function o = (Data_Function) (other);
    return params.equals(o.params) && body.equals(o.body);
  }
  
  @Override
  public int hashCode() {
    return 2 * params.hashCode() + 3 * body.hashCode();
  }
  
  public Data_Function withParams(java.util.List<hydra.langs.scala.meta.Data_Param> params) {
    if (params == null) {
      throw new IllegalArgumentException("null value for 'params' argument");
    }
    return new Data_Function(params, body);
  }
  
  public Data_Function withBody(hydra.langs.scala.meta.Data body) {
    if (body == null) {
      throw new IllegalArgumentException("null value for 'body' argument");
    }
    return new Data_Function(params, body);
  }
}