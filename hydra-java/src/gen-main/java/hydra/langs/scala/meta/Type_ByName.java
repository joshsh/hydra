package hydra.langs.scala.meta;

import java.io.Serializable;

public class Type_ByName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Type.ByName");
  
  public final hydra.langs.scala.meta.Type tpe;
  
  public Type_ByName (hydra.langs.scala.meta.Type tpe) {
    this.tpe = tpe;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Type_ByName)) {
      return false;
    }
    Type_ByName o = (Type_ByName) (other);
    return tpe.equals(o.tpe);
  }
  
  @Override
  public int hashCode() {
    return 2 * tpe.hashCode();
  }
}