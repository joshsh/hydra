package hydra.langs.scala.meta;

import java.io.Serializable;

public class Enumerator_Guard implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Enumerator.Guard");
  
  public final hydra.langs.scala.meta.Data cond;
  
  public Enumerator_Guard (hydra.langs.scala.meta.Data cond) {
    this.cond = cond;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Enumerator_Guard)) {
      return false;
    }
    Enumerator_Guard o = (Enumerator_Guard) (other);
    return cond.equals(o.cond);
  }
  
  @Override
  public int hashCode() {
    return 2 * cond.hashCode();
  }
}