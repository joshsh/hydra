package hydra.langs.scala.meta;

import java.io.Serializable;

public class Type_Var implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Type.Var");
  
  public final hydra.langs.scala.meta.Type_Name name;
  
  public Type_Var (hydra.langs.scala.meta.Type_Name name) {
    this.name = name;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Type_Var)) {
      return false;
    }
    Type_Var o = (Type_Var) (other);
    return name.equals(o.name);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode();
  }
}