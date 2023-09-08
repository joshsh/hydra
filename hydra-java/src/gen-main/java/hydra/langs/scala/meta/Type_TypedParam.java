package hydra.langs.scala.meta;

import java.io.Serializable;

public class Type_TypedParam implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Type.TypedParam");
  
  public final hydra.langs.scala.meta.Name name;
  
  public final hydra.langs.scala.meta.Type typ;
  
  public Type_TypedParam (hydra.langs.scala.meta.Name name, hydra.langs.scala.meta.Type typ) {
    this.name = name;
    this.typ = typ;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Type_TypedParam)) {
      return false;
    }
    Type_TypedParam o = (Type_TypedParam) (other);
    return name.equals(o.name) && typ.equals(o.typ);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * typ.hashCode();
  }
  
  public Type_TypedParam withName(hydra.langs.scala.meta.Name name) {
    return new Type_TypedParam(name, typ);
  }
  
  public Type_TypedParam withTyp(hydra.langs.scala.meta.Type typ) {
    return new Type_TypedParam(name, typ);
  }
}