package hydra.langs.scala.meta;

import java.io.Serializable;

public class Quasi implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Quasi");
  
  public Quasi () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Quasi)) {
      return false;
    }
    Quasi o = (Quasi) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}