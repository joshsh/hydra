package hydra.langs.scala.meta;

import java.io.Serializable;

public class Type_Param implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Type.Param");
  
  public final java.util.List<hydra.langs.scala.meta.Mod> mods;
  
  public final hydra.langs.scala.meta.Name name;
  
  public final java.util.List<hydra.langs.scala.meta.Type_Param> tparams;
  
  public final java.util.List<hydra.langs.scala.meta.Type_Bounds> tbounds;
  
  public final java.util.List<hydra.langs.scala.meta.Type> vbounds;
  
  public final java.util.List<hydra.langs.scala.meta.Type> cbounds;
  
  public Type_Param (java.util.List<hydra.langs.scala.meta.Mod> mods, hydra.langs.scala.meta.Name name, java.util.List<hydra.langs.scala.meta.Type_Param> tparams, java.util.List<hydra.langs.scala.meta.Type_Bounds> tbounds, java.util.List<hydra.langs.scala.meta.Type> vbounds, java.util.List<hydra.langs.scala.meta.Type> cbounds) {
    this.mods = mods;
    this.name = name;
    this.tparams = tparams;
    this.tbounds = tbounds;
    this.vbounds = vbounds;
    this.cbounds = cbounds;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Type_Param)) {
      return false;
    }
    Type_Param o = (Type_Param) (other);
    return mods.equals(o.mods) && name.equals(o.name) && tparams.equals(o.tparams) && tbounds.equals(o.tbounds) && vbounds.equals(o.vbounds) && cbounds.equals(o.cbounds);
  }
  
  @Override
  public int hashCode() {
    return 2 * mods.hashCode() + 3 * name.hashCode() + 5 * tparams.hashCode() + 7 * tbounds.hashCode() + 11 * vbounds.hashCode() + 13 * cbounds.hashCode();
  }
  
  public Type_Param withMods(java.util.List<hydra.langs.scala.meta.Mod> mods) {
    return new Type_Param(mods, name, tparams, tbounds, vbounds, cbounds);
  }
  
  public Type_Param withName(hydra.langs.scala.meta.Name name) {
    return new Type_Param(mods, name, tparams, tbounds, vbounds, cbounds);
  }
  
  public Type_Param withTparams(java.util.List<hydra.langs.scala.meta.Type_Param> tparams) {
    return new Type_Param(mods, name, tparams, tbounds, vbounds, cbounds);
  }
  
  public Type_Param withTbounds(java.util.List<hydra.langs.scala.meta.Type_Bounds> tbounds) {
    return new Type_Param(mods, name, tparams, tbounds, vbounds, cbounds);
  }
  
  public Type_Param withVbounds(java.util.List<hydra.langs.scala.meta.Type> vbounds) {
    return new Type_Param(mods, name, tparams, tbounds, vbounds, cbounds);
  }
  
  public Type_Param withCbounds(java.util.List<hydra.langs.scala.meta.Type> cbounds) {
    return new Type_Param(mods, name, tparams, tbounds, vbounds, cbounds);
  }
}