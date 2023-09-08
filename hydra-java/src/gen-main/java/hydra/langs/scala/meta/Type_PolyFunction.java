package hydra.langs.scala.meta;

import java.io.Serializable;

public class Type_PolyFunction implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Type.PolyFunction");
  
  public final java.util.List<hydra.langs.scala.meta.Type_Param> tparams;
  
  public final hydra.langs.scala.meta.Type tpe;
  
  public Type_PolyFunction (java.util.List<hydra.langs.scala.meta.Type_Param> tparams, hydra.langs.scala.meta.Type tpe) {
    this.tparams = tparams;
    this.tpe = tpe;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Type_PolyFunction)) {
      return false;
    }
    Type_PolyFunction o = (Type_PolyFunction) (other);
    return tparams.equals(o.tparams) && tpe.equals(o.tpe);
  }
  
  @Override
  public int hashCode() {
    return 2 * tparams.hashCode() + 3 * tpe.hashCode();
  }
  
  public Type_PolyFunction withTparams(java.util.List<hydra.langs.scala.meta.Type_Param> tparams) {
    return new Type_PolyFunction(tparams, tpe);
  }
  
  public Type_PolyFunction withTpe(hydra.langs.scala.meta.Type tpe) {
    return new Type_PolyFunction(tparams, tpe);
  }
}