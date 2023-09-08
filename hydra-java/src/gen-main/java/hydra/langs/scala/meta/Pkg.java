package hydra.langs.scala.meta;

import java.io.Serializable;

public class Pkg implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Pkg");
  
  public final hydra.langs.scala.meta.Data_Name name;
  
  public final hydra.langs.scala.meta.Data_Ref ref;
  
  public final java.util.List<hydra.langs.scala.meta.Stat> stats;
  
  public Pkg (hydra.langs.scala.meta.Data_Name name, hydra.langs.scala.meta.Data_Ref ref, java.util.List<hydra.langs.scala.meta.Stat> stats) {
    this.name = name;
    this.ref = ref;
    this.stats = stats;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Pkg)) {
      return false;
    }
    Pkg o = (Pkg) (other);
    return name.equals(o.name) && ref.equals(o.ref) && stats.equals(o.stats);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * ref.hashCode() + 5 * stats.hashCode();
  }
  
  public Pkg withName(hydra.langs.scala.meta.Data_Name name) {
    return new Pkg(name, ref, stats);
  }
  
  public Pkg withRef(hydra.langs.scala.meta.Data_Ref ref) {
    return new Pkg(name, ref, stats);
  }
  
  public Pkg withStats(java.util.List<hydra.langs.scala.meta.Stat> stats) {
    return new Pkg(name, ref, stats);
  }
}