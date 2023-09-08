package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_Anonymous implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.Anonymous");
  
  public Data_Anonymous () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_Anonymous)) {
      return false;
    }
    Data_Anonymous o = (Data_Anonymous) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}