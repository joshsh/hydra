package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_Assign implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.Assign");
  
  public final hydra.langs.scala.meta.Data lhs;
  
  public final hydra.langs.scala.meta.Data rhs;
  
  public Data_Assign (hydra.langs.scala.meta.Data lhs, hydra.langs.scala.meta.Data rhs) {
    this.lhs = lhs;
    this.rhs = rhs;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_Assign)) {
      return false;
    }
    Data_Assign o = (Data_Assign) (other);
    return lhs.equals(o.lhs) && rhs.equals(o.rhs);
  }
  
  @Override
  public int hashCode() {
    return 2 * lhs.hashCode() + 3 * rhs.hashCode();
  }
  
  public Data_Assign withLhs(hydra.langs.scala.meta.Data lhs) {
    return new Data_Assign(lhs, rhs);
  }
  
  public Data_Assign withRhs(hydra.langs.scala.meta.Data rhs) {
    return new Data_Assign(lhs, rhs);
  }
}