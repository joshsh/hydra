package hydra.langs.scala.meta;

import java.io.Serializable;

public class Type_Tuple implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Type.Tuple");
  
  public final java.util.List<hydra.langs.scala.meta.Type> args;
  
  public Type_Tuple (java.util.List<hydra.langs.scala.meta.Type> args) {
    this.args = args;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Type_Tuple)) {
      return false;
    }
    Type_Tuple o = (Type_Tuple) (other);
    return args.equals(o.args);
  }
  
  @Override
  public int hashCode() {
    return 2 * args.hashCode();
  }
}