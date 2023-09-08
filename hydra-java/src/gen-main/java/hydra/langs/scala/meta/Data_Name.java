package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_Name implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.Name");
  
  public final hydra.langs.scala.meta.PredefString value;
  
  public Data_Name (hydra.langs.scala.meta.PredefString value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_Name)) {
      return false;
    }
    Data_Name o = (Data_Name) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}