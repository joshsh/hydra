package hydra.langs.scala.meta;

import java.io.Serializable;

public class Pat_Var implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Pat.Var");
  
  public final hydra.langs.scala.meta.Data_Name name;
  
  public Pat_Var (hydra.langs.scala.meta.Data_Name name) {
    this.name = name;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Pat_Var)) {
      return false;
    }
    Pat_Var o = (Pat_Var) (other);
    return name.equals(o.name);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode();
  }
}