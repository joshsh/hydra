package hydra.langs.scala.meta;

import java.io.Serializable;

public class Type_Project implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Type.Project");
  
  public final hydra.langs.scala.meta.Type qual;
  
  public final hydra.langs.scala.meta.Type_Name name;
  
  public Type_Project (hydra.langs.scala.meta.Type qual, hydra.langs.scala.meta.Type_Name name) {
    this.qual = qual;
    this.name = name;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Type_Project)) {
      return false;
    }
    Type_Project o = (Type_Project) (other);
    return qual.equals(o.qual) && name.equals(o.name);
  }
  
  @Override
  public int hashCode() {
    return 2 * qual.hashCode() + 3 * name.hashCode();
  }
  
  public Type_Project withQual(hydra.langs.scala.meta.Type qual) {
    return new Type_Project(qual, name);
  }
  
  public Type_Project withName(hydra.langs.scala.meta.Type_Name name) {
    return new Type_Project(qual, name);
  }
}