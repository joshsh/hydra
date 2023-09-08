package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_This implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.This");
  
  public Data_This () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_This)) {
      return false;
    }
    Data_This o = (Data_This) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}