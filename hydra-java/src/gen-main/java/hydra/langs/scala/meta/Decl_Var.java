package hydra.langs.scala.meta;

import java.io.Serializable;

public class Decl_Var implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Decl.Var");
  
  public final java.util.List<hydra.langs.scala.meta.Mod> mods;
  
  public final java.util.List<hydra.langs.scala.meta.Pat> pats;
  
  public final hydra.langs.scala.meta.Type decltpe;
  
  public Decl_Var (java.util.List<hydra.langs.scala.meta.Mod> mods, java.util.List<hydra.langs.scala.meta.Pat> pats, hydra.langs.scala.meta.Type decltpe) {
    this.mods = mods;
    this.pats = pats;
    this.decltpe = decltpe;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Decl_Var)) {
      return false;
    }
    Decl_Var o = (Decl_Var) (other);
    return mods.equals(o.mods) && pats.equals(o.pats) && decltpe.equals(o.decltpe);
  }
  
  @Override
  public int hashCode() {
    return 2 * mods.hashCode() + 3 * pats.hashCode() + 5 * decltpe.hashCode();
  }
  
  public Decl_Var withMods(java.util.List<hydra.langs.scala.meta.Mod> mods) {
    return new Decl_Var(mods, pats, decltpe);
  }
  
  public Decl_Var withPats(java.util.List<hydra.langs.scala.meta.Pat> pats) {
    return new Decl_Var(mods, pats, decltpe);
  }
  
  public Decl_Var withDecltpe(hydra.langs.scala.meta.Type decltpe) {
    return new Decl_Var(mods, pats, decltpe);
  }
}