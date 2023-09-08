package hydra.langs.scala.meta;

import java.io.Serializable;

public class Template implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Template");
  
  public final java.util.List<hydra.langs.scala.meta.Stat> early;
  
  public final java.util.List<hydra.langs.scala.meta.Init> inits;
  
  public final hydra.langs.scala.meta.Self self;
  
  public final java.util.List<hydra.langs.scala.meta.Stat> stats;
  
  public Template (java.util.List<hydra.langs.scala.meta.Stat> early, java.util.List<hydra.langs.scala.meta.Init> inits, hydra.langs.scala.meta.Self self, java.util.List<hydra.langs.scala.meta.Stat> stats) {
    this.early = early;
    this.inits = inits;
    this.self = self;
    this.stats = stats;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Template)) {
      return false;
    }
    Template o = (Template) (other);
    return early.equals(o.early) && inits.equals(o.inits) && self.equals(o.self) && stats.equals(o.stats);
  }
  
  @Override
  public int hashCode() {
    return 2 * early.hashCode() + 3 * inits.hashCode() + 5 * self.hashCode() + 7 * stats.hashCode();
  }
  
  public Template withEarly(java.util.List<hydra.langs.scala.meta.Stat> early) {
    return new Template(early, inits, self, stats);
  }
  
  public Template withInits(java.util.List<hydra.langs.scala.meta.Init> inits) {
    return new Template(early, inits, self, stats);
  }
  
  public Template withSelf(hydra.langs.scala.meta.Self self) {
    return new Template(early, inits, self, stats);
  }
  
  public Template withStats(java.util.List<hydra.langs.scala.meta.Stat> stats) {
    return new Template(early, inits, self, stats);
  }
}