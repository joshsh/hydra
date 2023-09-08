package hydra.langs.scala.meta;

import java.io.Serializable;

public class Importee_Given implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Importee.Given");
  
  public final hydra.langs.scala.meta.Type tpe;
  
  public Importee_Given (hydra.langs.scala.meta.Type tpe) {
    this.tpe = tpe;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Importee_Given)) {
      return false;
    }
    Importee_Given o = (Importee_Given) (other);
    return tpe.equals(o.tpe);
  }
  
  @Override
  public int hashCode() {
    return 2 * tpe.hashCode();
  }
}