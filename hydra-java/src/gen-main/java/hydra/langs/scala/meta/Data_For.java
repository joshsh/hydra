package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_For implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.For");
  
  public final java.util.List<hydra.langs.scala.meta.Enumerator> enums;
  
  public Data_For (java.util.List<hydra.langs.scala.meta.Enumerator> enums) {
    this.enums = enums;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_For)) {
      return false;
    }
    Data_For o = (Data_For) (other);
    return enums.equals(o.enums);
  }
  
  @Override
  public int hashCode() {
    return 2 * enums.hashCode();
  }
}