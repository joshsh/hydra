package hydra.langs.scala.meta;

import java.io.Serializable;

public class Defn_RepeatedEnumCase implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Defn.RepeatedEnumCase");
  
  public final java.util.List<hydra.langs.scala.meta.Mod> mods;
  
  public final java.util.List<hydra.langs.scala.meta.Data_Name> cases;
  
  public Defn_RepeatedEnumCase (java.util.List<hydra.langs.scala.meta.Mod> mods, java.util.List<hydra.langs.scala.meta.Data_Name> cases) {
    this.mods = mods;
    this.cases = cases;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Defn_RepeatedEnumCase)) {
      return false;
    }
    Defn_RepeatedEnumCase o = (Defn_RepeatedEnumCase) (other);
    return mods.equals(o.mods) && cases.equals(o.cases);
  }
  
  @Override
  public int hashCode() {
    return 2 * mods.hashCode() + 3 * cases.hashCode();
  }
  
  public Defn_RepeatedEnumCase withMods(java.util.List<hydra.langs.scala.meta.Mod> mods) {
    return new Defn_RepeatedEnumCase(mods, cases);
  }
  
  public Defn_RepeatedEnumCase withCases(java.util.List<hydra.langs.scala.meta.Data_Name> cases) {
    return new Defn_RepeatedEnumCase(mods, cases);
  }
}