package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_Select implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.Select");
  
  public final hydra.langs.scala.meta.Data qual;
  
  public final hydra.langs.scala.meta.Data_Name name;
  
  public Data_Select (hydra.langs.scala.meta.Data qual, hydra.langs.scala.meta.Data_Name name) {
    this.qual = qual;
    this.name = name;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_Select)) {
      return false;
    }
    Data_Select o = (Data_Select) (other);
    return qual.equals(o.qual) && name.equals(o.name);
  }
  
  @Override
  public int hashCode() {
    return 2 * qual.hashCode() + 3 * name.hashCode();
  }
  
  public Data_Select withQual(hydra.langs.scala.meta.Data qual) {
    return new Data_Select(qual, name);
  }
  
  public Data_Select withName(hydra.langs.scala.meta.Data_Name name) {
    return new Data_Select(qual, name);
  }
}