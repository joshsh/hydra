package hydra.langs.java.syntax;

import java.io.Serializable;

public class ForCond implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ForCond");
  
  public final java.util.Optional<hydra.langs.java.syntax.ForInit> init;
  
  public final java.util.Optional<hydra.langs.java.syntax.Expression> cond;
  
  public final java.util.Optional<hydra.langs.java.syntax.ForUpdate> update;
  
  public ForCond (java.util.Optional<hydra.langs.java.syntax.ForInit> init, java.util.Optional<hydra.langs.java.syntax.Expression> cond, java.util.Optional<hydra.langs.java.syntax.ForUpdate> update) {
    this.init = init;
    this.cond = cond;
    this.update = update;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ForCond)) {
      return false;
    }
    ForCond o = (ForCond) (other);
    return init.equals(o.init) && cond.equals(o.cond) && update.equals(o.update);
  }
  
  @Override
  public int hashCode() {
    return 2 * init.hashCode() + 3 * cond.hashCode() + 5 * update.hashCode();
  }
  
  public ForCond withInit(java.util.Optional<hydra.langs.java.syntax.ForInit> init) {
    return new ForCond(init, cond, update);
  }
  
  public ForCond withCond(java.util.Optional<hydra.langs.java.syntax.Expression> cond) {
    return new ForCond(init, cond, update);
  }
  
  public ForCond withUpdate(java.util.Optional<hydra.langs.java.syntax.ForUpdate> update) {
    return new ForCond(init, cond, update);
  }
}