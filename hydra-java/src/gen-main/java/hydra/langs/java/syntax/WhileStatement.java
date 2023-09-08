package hydra.langs.java.syntax;

import java.io.Serializable;

public class WhileStatement implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.WhileStatement");
  
  public final java.util.Optional<hydra.langs.java.syntax.Expression> cond;
  
  public final hydra.langs.java.syntax.Statement body;
  
  public WhileStatement (java.util.Optional<hydra.langs.java.syntax.Expression> cond, hydra.langs.java.syntax.Statement body) {
    this.cond = cond;
    this.body = body;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof WhileStatement)) {
      return false;
    }
    WhileStatement o = (WhileStatement) (other);
    return cond.equals(o.cond) && body.equals(o.body);
  }
  
  @Override
  public int hashCode() {
    return 2 * cond.hashCode() + 3 * body.hashCode();
  }
  
  public WhileStatement withCond(java.util.Optional<hydra.langs.java.syntax.Expression> cond) {
    return new WhileStatement(cond, body);
  }
  
  public WhileStatement withBody(hydra.langs.java.syntax.Statement body) {
    return new WhileStatement(cond, body);
  }
}