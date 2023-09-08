package hydra.langs.scala.meta;

import java.io.Serializable;

public class Defn_Val implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Defn.Val");
  
  public final java.util.List<hydra.langs.scala.meta.Mod> mods;
  
  public final java.util.List<hydra.langs.scala.meta.Pat> pats;
  
  public final java.util.Optional<hydra.langs.scala.meta.Type> decltpe;
  
  public final hydra.langs.scala.meta.Data rhs;
  
  public Defn_Val (java.util.List<hydra.langs.scala.meta.Mod> mods, java.util.List<hydra.langs.scala.meta.Pat> pats, java.util.Optional<hydra.langs.scala.meta.Type> decltpe, hydra.langs.scala.meta.Data rhs) {
    this.mods = mods;
    this.pats = pats;
    this.decltpe = decltpe;
    this.rhs = rhs;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Defn_Val)) {
      return false;
    }
    Defn_Val o = (Defn_Val) (other);
    return mods.equals(o.mods) && pats.equals(o.pats) && decltpe.equals(o.decltpe) && rhs.equals(o.rhs);
  }
  
  @Override
  public int hashCode() {
    return 2 * mods.hashCode() + 3 * pats.hashCode() + 5 * decltpe.hashCode() + 7 * rhs.hashCode();
  }
  
  public Defn_Val withMods(java.util.List<hydra.langs.scala.meta.Mod> mods) {
    return new Defn_Val(mods, pats, decltpe, rhs);
  }
  
  public Defn_Val withPats(java.util.List<hydra.langs.scala.meta.Pat> pats) {
    return new Defn_Val(mods, pats, decltpe, rhs);
  }
  
  public Defn_Val withDecltpe(java.util.Optional<hydra.langs.scala.meta.Type> decltpe) {
    return new Defn_Val(mods, pats, decltpe, rhs);
  }
  
  public Defn_Val withRhs(hydra.langs.scala.meta.Data rhs) {
    return new Defn_Val(mods, pats, decltpe, rhs);
  }
}