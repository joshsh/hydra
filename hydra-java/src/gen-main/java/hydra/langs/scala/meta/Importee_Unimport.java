package hydra.langs.scala.meta;

import java.io.Serializable;

public class Importee_Unimport implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Importee.Unimport");
  
  public final hydra.langs.scala.meta.Name name;
  
  public Importee_Unimport (hydra.langs.scala.meta.Name name) {
    this.name = name;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Importee_Unimport)) {
      return false;
    }
    Importee_Unimport o = (Importee_Unimport) (other);
    return name.equals(o.name);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode();
  }
}