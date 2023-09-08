package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_Block implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.Block");
  
  public final java.util.List<hydra.langs.scala.meta.Stat> stats;
  
  public Data_Block (java.util.List<hydra.langs.scala.meta.Stat> stats) {
    this.stats = stats;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_Block)) {
      return false;
    }
    Data_Block o = (Data_Block) (other);
    return stats.equals(o.stats);
  }
  
  @Override
  public int hashCode() {
    return 2 * stats.hashCode();
  }
}