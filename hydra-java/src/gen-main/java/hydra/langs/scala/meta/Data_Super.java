// Note: this is an automatically generated file. Do not edit.

package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_Super implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.Super");
  
  public static final hydra.core.Name FIELD_NAME_THISP = new hydra.core.Name("thisp");
  
  public static final hydra.core.Name FIELD_NAME_SUPERP = new hydra.core.Name("superp");
  
  public final hydra.langs.scala.meta.Name thisp;
  
  public final hydra.langs.scala.meta.Name superp;
  
  public Data_Super (hydra.langs.scala.meta.Name thisp, hydra.langs.scala.meta.Name superp) {
    java.util.Objects.requireNonNull((thisp));
    java.util.Objects.requireNonNull((superp));
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
    java.util.Objects.requireNonNull((thisp));
    return new Data_Super(thisp, superp);
  }
  
  public Data_Super withSuperp(hydra.langs.scala.meta.Name superp) {
    java.util.Objects.requireNonNull((superp));
    return new Data_Super(thisp, superp);
  }
}