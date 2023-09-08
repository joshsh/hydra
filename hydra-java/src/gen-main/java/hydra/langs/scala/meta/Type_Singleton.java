package hydra.langs.scala.meta;

import java.io.Serializable;

public class Type_Singleton implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Type.Singleton");
  
  public final hydra.langs.scala.meta.Data_Ref ref;
  
  public Type_Singleton (hydra.langs.scala.meta.Data_Ref ref) {
    this.ref = ref;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Type_Singleton)) {
      return false;
    }
    Type_Singleton o = (Type_Singleton) (other);
    return ref.equals(o.ref);
  }
  
  @Override
  public int hashCode() {
    return 2 * ref.hashCode();
  }
}