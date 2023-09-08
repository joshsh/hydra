package hydra.langs.scala.meta;

import java.io.Serializable;

public class Pat_Extract implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Pat.Extract");
  
  public final hydra.langs.scala.meta.Data fun;
  
  public final java.util.List<hydra.langs.scala.meta.Pat> args;
  
  public Pat_Extract (hydra.langs.scala.meta.Data fun, java.util.List<hydra.langs.scala.meta.Pat> args) {
    this.fun = fun;
    this.args = args;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Pat_Extract)) {
      return false;
    }
    Pat_Extract o = (Pat_Extract) (other);
    return fun.equals(o.fun) && args.equals(o.args);
  }
  
  @Override
  public int hashCode() {
    return 2 * fun.hashCode() + 3 * args.hashCode();
  }
  
  public Pat_Extract withFun(hydra.langs.scala.meta.Data fun) {
    return new Pat_Extract(fun, args);
  }
  
  public Pat_Extract withArgs(java.util.List<hydra.langs.scala.meta.Pat> args) {
    return new Pat_Extract(fun, args);
  }
}