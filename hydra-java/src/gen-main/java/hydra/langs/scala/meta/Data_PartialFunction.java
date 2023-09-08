package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_PartialFunction implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.PartialFunction");
  
  public final java.util.List<hydra.langs.scala.meta.Case> cases;
  
  public Data_PartialFunction (java.util.List<hydra.langs.scala.meta.Case> cases) {
    this.cases = cases;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_PartialFunction)) {
      return false;
    }
    Data_PartialFunction o = (Data_PartialFunction) (other);
    return cases.equals(o.cases);
  }
  
  @Override
  public int hashCode() {
    return 2 * cases.hashCode();
  }
}