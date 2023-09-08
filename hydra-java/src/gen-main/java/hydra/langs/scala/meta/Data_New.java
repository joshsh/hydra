package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_New implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.New");
  
  public final hydra.langs.scala.meta.Init init;
  
  public Data_New (hydra.langs.scala.meta.Init init) {
    this.init = init;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_New)) {
      return false;
    }
    Data_New o = (Data_New) (other);
    return init.equals(o.init);
  }
  
  @Override
  public int hashCode() {
    return 2 * init.hashCode();
  }
}