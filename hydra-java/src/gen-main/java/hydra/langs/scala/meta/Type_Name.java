package hydra.langs.scala.meta;

import java.io.Serializable;

public class Type_Name implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Type.Name");
  
  public final String value;
  
  public Type_Name (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Type_Name)) {
      return false;
    }
    Type_Name o = (Type_Name) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}