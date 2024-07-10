// Note: this is an automatically generated file. Do not edit.

package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_ApplyUsing implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.ApplyUsing");
  
  public final hydra.langs.scala.meta.Data fun;
  
  public final java.util.List<hydra.langs.scala.meta.Data> targs;
  
  public Data_ApplyUsing (hydra.langs.scala.meta.Data fun, java.util.List<hydra.langs.scala.meta.Data> targs) {
    if (fun == null) {
      throw new IllegalArgumentException("null value for 'fun' argument");
    }
    if (targs == null) {
      throw new IllegalArgumentException("null value for 'targs' argument");
    }
    this.fun = fun;
    this.targs = targs;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_ApplyUsing)) {
      return false;
    }
    Data_ApplyUsing o = (Data_ApplyUsing) (other);
    return fun.equals(o.fun) && targs.equals(o.targs);
  }
  
  @Override
  public int hashCode() {
    return 2 * fun.hashCode() + 3 * targs.hashCode();
  }
  
  public Data_ApplyUsing withFun(hydra.langs.scala.meta.Data fun) {
    if (fun == null) {
      throw new IllegalArgumentException("null value for 'fun' argument");
    }
    return new Data_ApplyUsing(fun, targs);
  }
  
  public Data_ApplyUsing withTargs(java.util.List<hydra.langs.scala.meta.Data> targs) {
    if (targs == null) {
      throw new IllegalArgumentException("null value for 'targs' argument");
    }
    return new Data_ApplyUsing(fun, targs);
  }
}