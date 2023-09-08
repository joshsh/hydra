package hydra.langs.scala.meta;

import java.io.Serializable;

public class Pat_Tuple implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Pat.Tuple");
  
  public final java.util.List<hydra.langs.scala.meta.Pat> args;
  
  public Pat_Tuple (java.util.List<hydra.langs.scala.meta.Pat> args) {
    this.args = args;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Pat_Tuple)) {
      return false;
    }
    Pat_Tuple o = (Pat_Tuple) (other);
    return args.equals(o.args);
  }
  
  @Override
  public int hashCode() {
    return 2 * args.hashCode();
  }
}