package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_ForYield implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.ForYield");
  
  public final java.util.List<hydra.langs.scala.meta.Enumerator> enums;
  
  public Data_ForYield (java.util.List<hydra.langs.scala.meta.Enumerator> enums) {
    this.enums = enums;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_ForYield)) {
      return false;
    }
    Data_ForYield o = (Data_ForYield) (other);
    return enums.equals(o.enums);
  }
  
  @Override
  public int hashCode() {
    return 2 * enums.hashCode();
  }
}