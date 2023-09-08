package hydra.langs.scala.meta;

import java.io.Serializable;

public class Mod_Annot implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Mod.Annot");
  
  public final hydra.langs.scala.meta.Init init;
  
  public Mod_Annot (hydra.langs.scala.meta.Init init) {
    this.init = init;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Mod_Annot)) {
      return false;
    }
    Mod_Annot o = (Mod_Annot) (other);
    return init.equals(o.init);
  }
  
  @Override
  public int hashCode() {
    return 2 * init.hashCode();
  }
}