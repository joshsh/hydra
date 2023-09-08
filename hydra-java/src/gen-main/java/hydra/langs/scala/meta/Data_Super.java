package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_Super implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.Super");
  
  public final hydra.langs.scala.meta.Name thisp;
  
  public final hydra.langs.scala.meta.Name superp;
  
  public Data_Super (hydra.langs.scala.meta.Name thisp, hydra.langs.scala.meta.Name superp) {
    this.thisp = thisp;
    this.superp = superp;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_Super)) {
      return false;
    }
    Data_Super o = (Data_Super) (other);
    return thisp.equals(o.thisp) && superp.equals(o.superp);
  }
  
  @Override
  public int hashCode() {
    return 2 * thisp.hashCode() + 3 * superp.hashCode();
  }
  
  public Data_Super withThisp(hydra.langs.scala.meta.Name thisp) {
    return new Data_Super(thisp, superp);
  }
  
  public Data_Super withSuperp(hydra.langs.scala.meta.Name superp) {
    return new Data_Super(thisp, superp);
  }
}