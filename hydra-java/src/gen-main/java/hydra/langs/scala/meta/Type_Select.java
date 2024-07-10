// Note: this is an automatically generated file. Do not edit.

package hydra.langs.scala.meta;

import java.io.Serializable;

public class Type_Select implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Type.Select");
  
  public final hydra.langs.scala.meta.Data_Ref qual;
  
  public final hydra.langs.scala.meta.Type_Name name;
  
  public Type_Select (hydra.langs.scala.meta.Data_Ref qual, hydra.langs.scala.meta.Type_Name name) {
    if (qual == null) {
      throw new IllegalArgumentException("null value for 'qual' argument");
    }
    if (name == null) {
      throw new IllegalArgumentException("null value for 'name' argument");
    }
    this.qual = qual;
    this.name = name;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Type_Select)) {
      return false;
    }
    Type_Select o = (Type_Select) (other);
    return qual.equals(o.qual) && name.equals(o.name);
  }
  
  @Override
  public int hashCode() {
    return 2 * qual.hashCode() + 3 * name.hashCode();
  }
  
  public Type_Select withQual(hydra.langs.scala.meta.Data_Ref qual) {
    if (qual == null) {
      throw new IllegalArgumentException("null value for 'qual' argument");
    }
    return new Type_Select(qual, name);
  }
  
  public Type_Select withName(hydra.langs.scala.meta.Type_Name name) {
    if (name == null) {
      throw new IllegalArgumentException("null value for 'name' argument");
    }
    return new Type_Select(qual, name);
  }
}