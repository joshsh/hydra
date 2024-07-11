// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class ForCond implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ForCond");
  
  public final hydra.util.Opt<hydra.langs.java.syntax.ForInit> init;
  
  public final hydra.util.Opt<hydra.langs.java.syntax.Expression> cond;
  
  public final hydra.util.Opt<hydra.langs.java.syntax.ForUpdate> update;
  
  public ForCond (hydra.util.Opt<hydra.langs.java.syntax.ForInit> init, hydra.util.Opt<hydra.langs.java.syntax.Expression> cond, hydra.util.Opt<hydra.langs.java.syntax.ForUpdate> update) {
    if (init == null) {
      throw new IllegalArgumentException("null value for 'init' argument");
    }
    if (cond == null) {
      throw new IllegalArgumentException("null value for 'cond' argument");
    }
    if (update == null) {
      throw new IllegalArgumentException("null value for 'update' argument");
    }
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
  
  public ForCond withInit(hydra.util.Opt<hydra.langs.java.syntax.ForInit> init) {
    if (init == null) {
      throw new IllegalArgumentException("null value for 'init' argument");
    }
    return new ForCond(init, cond, update);
  }
  
  public ForCond withCond(hydra.util.Opt<hydra.langs.java.syntax.Expression> cond) {
    if (cond == null) {
      throw new IllegalArgumentException("null value for 'cond' argument");
    }
    return new ForCond(init, cond, update);
  }
  
  public ForCond withUpdate(hydra.util.Opt<hydra.langs.java.syntax.ForUpdate> update) {
    if (update == null) {
      throw new IllegalArgumentException("null value for 'update' argument");
    }
    return new ForCond(init, cond, update);
  }
}