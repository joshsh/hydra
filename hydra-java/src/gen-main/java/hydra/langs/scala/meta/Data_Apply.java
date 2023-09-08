package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_Apply implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.Apply");
  
  public final hydra.langs.scala.meta.Data fun;
  
  public final java.util.List<hydra.langs.scala.meta.Data> args;
  
  public Data_Apply (hydra.langs.scala.meta.Data fun, java.util.List<hydra.langs.scala.meta.Data> args) {
    this.fun = fun;
    this.args = args;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_Apply)) {
      return false;
    }
    Data_Apply o = (Data_Apply) (other);
    return fun.equals(o.fun) && args.equals(o.args);
  }
  
  @Override
  public int hashCode() {
    return 2 * fun.hashCode() + 3 * args.hashCode();
  }
  
  public Data_Apply withFun(hydra.langs.scala.meta.Data fun) {
    return new Data_Apply(fun, args);
  }
  
  public Data_Apply withArgs(java.util.List<hydra.langs.scala.meta.Data> args) {
    return new Data_Apply(fun, args);
  }
}