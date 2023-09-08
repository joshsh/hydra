package hydra.langs.scala.meta;

import java.io.Serializable;

public class Pat_Given implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Pat.Given");
  
  public final hydra.langs.scala.meta.Type tpe;
  
  public Pat_Given (hydra.langs.scala.meta.Type tpe) {
    this.tpe = tpe;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Pat_Given)) {
      return false;
    }
    Pat_Given o = (Pat_Given) (other);
    return tpe.equals(o.tpe);
  }
  
  @Override
  public int hashCode() {
    return 2 * tpe.hashCode();
  }
}