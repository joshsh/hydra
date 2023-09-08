package hydra.langs.scala.meta;

import java.io.Serializable;

public class Ctor_Secondary implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Ctor.Secondary");
  
  public final java.util.List<hydra.langs.scala.meta.Mod> mods;
  
  public final hydra.langs.scala.meta.Name name;
  
  public final java.util.List<java.util.List<hydra.langs.scala.meta.Data_Param>> paramss;
  
  public final hydra.langs.scala.meta.Init init;
  
  public final java.util.List<hydra.langs.scala.meta.Stat> stats;
  
  public Ctor_Secondary (java.util.List<hydra.langs.scala.meta.Mod> mods, hydra.langs.scala.meta.Name name, java.util.List<java.util.List<hydra.langs.scala.meta.Data_Param>> paramss, hydra.langs.scala.meta.Init init, java.util.List<hydra.langs.scala.meta.Stat> stats) {
    this.mods = mods;
    this.name = name;
    this.paramss = paramss;
    this.init = init;
    this.stats = stats;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Ctor_Secondary)) {
      return false;
    }
    Ctor_Secondary o = (Ctor_Secondary) (other);
    return mods.equals(o.mods) && name.equals(o.name) && paramss.equals(o.paramss) && init.equals(o.init) && stats.equals(o.stats);
  }
  
  @Override
  public int hashCode() {
    return 2 * mods.hashCode() + 3 * name.hashCode() + 5 * paramss.hashCode() + 7 * init.hashCode() + 11 * stats.hashCode();
  }
  
  public Ctor_Secondary withMods(java.util.List<hydra.langs.scala.meta.Mod> mods) {
    return new Ctor_Secondary(mods, name, paramss, init, stats);
  }
  
  public Ctor_Secondary withName(hydra.langs.scala.meta.Name name) {
    return new Ctor_Secondary(mods, name, paramss, init, stats);
  }
  
  public Ctor_Secondary withParamss(java.util.List<java.util.List<hydra.langs.scala.meta.Data_Param>> paramss) {
    return new Ctor_Secondary(mods, name, paramss, init, stats);
  }
  
  public Ctor_Secondary withInit(hydra.langs.scala.meta.Init init) {
    return new Ctor_Secondary(mods, name, paramss, init, stats);
  }
  
  public Ctor_Secondary withStats(java.util.List<hydra.langs.scala.meta.Stat> stats) {
    return new Ctor_Secondary(mods, name, paramss, init, stats);
  }
}