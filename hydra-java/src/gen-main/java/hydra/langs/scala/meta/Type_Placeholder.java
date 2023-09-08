package hydra.langs.scala.meta;

import java.io.Serializable;

public class Type_Placeholder implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Type.Placeholder");
  
  public final hydra.langs.scala.meta.Type_Bounds bounds;
  
  public Type_Placeholder (hydra.langs.scala.meta.Type_Bounds bounds) {
    this.bounds = bounds;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Type_Placeholder)) {
      return false;
    }
    Type_Placeholder o = (Type_Placeholder) (other);
    return bounds.equals(o.bounds);
  }
  
  @Override
  public int hashCode() {
    return 2 * bounds.hashCode();
  }
}