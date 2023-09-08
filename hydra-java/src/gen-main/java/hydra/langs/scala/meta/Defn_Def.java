package hydra.langs.scala.meta;

import java.io.Serializable;

public class Defn_Def implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Defn.Def");
  
  public final java.util.List<hydra.langs.scala.meta.Mod> mods;
  
  public final hydra.langs.scala.meta.Data_Name name;
  
  public final java.util.List<hydra.langs.scala.meta.Type_Param> tparams;
  
  public final java.util.List<java.util.List<hydra.langs.scala.meta.Data_Param>> paramss;
  
  public final java.util.Optional<hydra.langs.scala.meta.Type> decltpe;
  
  public final hydra.langs.scala.meta.Data body;
  
  public Defn_Def (java.util.List<hydra.langs.scala.meta.Mod> mods, hydra.langs.scala.meta.Data_Name name, java.util.List<hydra.langs.scala.meta.Type_Param> tparams, java.util.List<java.util.List<hydra.langs.scala.meta.Data_Param>> paramss, java.util.Optional<hydra.langs.scala.meta.Type> decltpe, hydra.langs.scala.meta.Data body) {
    this.mods = mods;
    this.name = name;
    this.tparams = tparams;
    this.paramss = paramss;
    this.decltpe = decltpe;
    this.body = body;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Defn_Def)) {
      return false;
    }
    Defn_Def o = (Defn_Def) (other);
    return mods.equals(o.mods) && name.equals(o.name) && tparams.equals(o.tparams) && paramss.equals(o.paramss) && decltpe.equals(o.decltpe) && body.equals(o.body);
  }
  
  @Override
  public int hashCode() {
    return 2 * mods.hashCode() + 3 * name.hashCode() + 5 * tparams.hashCode() + 7 * paramss.hashCode() + 11 * decltpe.hashCode() + 13 * body.hashCode();
  }
  
  public Defn_Def withMods(java.util.List<hydra.langs.scala.meta.Mod> mods) {
    return new Defn_Def(mods, name, tparams, paramss, decltpe, body);
  }
  
  public Defn_Def withName(hydra.langs.scala.meta.Data_Name name) {
    return new Defn_Def(mods, name, tparams, paramss, decltpe, body);
  }
  
  public Defn_Def withTparams(java.util.List<hydra.langs.scala.meta.Type_Param> tparams) {
    return new Defn_Def(mods, name, tparams, paramss, decltpe, body);
  }
  
  public Defn_Def withParamss(java.util.List<java.util.List<hydra.langs.scala.meta.Data_Param>> paramss) {
    return new Defn_Def(mods, name, tparams, paramss, decltpe, body);
  }
  
  public Defn_Def withDecltpe(java.util.Optional<hydra.langs.scala.meta.Type> decltpe) {
    return new Defn_Def(mods, name, tparams, paramss, decltpe, body);
  }
  
  public Defn_Def withBody(hydra.langs.scala.meta.Data body) {
    return new Defn_Def(mods, name, tparams, paramss, decltpe, body);
  }
}