package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_EndMarker implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.EndMarker");
  
  public final hydra.langs.scala.meta.Data_Name name;
  
  public Data_EndMarker (hydra.langs.scala.meta.Data_Name name) {
    this.name = name;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_EndMarker)) {
      return false;
    }
    Data_EndMarker o = (Data_EndMarker) (other);
    return name.equals(o.name);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode();
  }
}