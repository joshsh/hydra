package hydra.langs.scala.meta;

import java.io.Serializable;

public class Type_AnonymousName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Type.AnonymousName");
  
  public Type_AnonymousName () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Type_AnonymousName)) {
      return false;
    }
    Type_AnonymousName o = (Type_AnonymousName) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}