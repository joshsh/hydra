package hydra.langs.scala.meta;

import java.io.Serializable;

public class Pat_Macro implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Pat.Macro");
  
  public final hydra.langs.scala.meta.Data body;
  
  public Pat_Macro (hydra.langs.scala.meta.Data body) {
    this.body = body;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Pat_Macro)) {
      return false;
    }
    Pat_Macro o = (Pat_Macro) (other);
    return body.equals(o.body);
  }
  
  @Override
  public int hashCode() {
    return 2 * body.hashCode();
  }
}