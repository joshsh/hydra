package hydra.langs.scala.meta;

import java.io.Serializable;

public class Pat_Repeated implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Pat.Repeated");
  
  public final hydra.langs.scala.meta.Data_Name name;
  
  public Pat_Repeated (hydra.langs.scala.meta.Data_Name name) {
    this.name = name;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Pat_Repeated)) {
      return false;
    }
    Pat_Repeated o = (Pat_Repeated) (other);
    return name.equals(o.name);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode();
  }
}