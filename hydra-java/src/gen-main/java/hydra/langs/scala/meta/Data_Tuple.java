package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_Tuple implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.Tuple");
  
  public final java.util.List<hydra.langs.scala.meta.Data> args;
  
  public Data_Tuple (java.util.List<hydra.langs.scala.meta.Data> args) {
    this.args = args;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_Tuple)) {
      return false;
    }
    Data_Tuple o = (Data_Tuple) (other);
    return args.equals(o.args);
  }
  
  @Override
  public int hashCode() {
    return 2 * args.hashCode();
  }
}