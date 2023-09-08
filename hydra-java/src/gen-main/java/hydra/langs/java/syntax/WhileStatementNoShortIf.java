package hydra.langs.java.syntax;

import java.io.Serializable;

public class WhileStatementNoShortIf implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.WhileStatementNoShortIf");
  
  public final java.util.Optional<hydra.langs.java.syntax.Expression> cond;
  
  public final hydra.langs.java.syntax.StatementNoShortIf body;
  
  public WhileStatementNoShortIf (java.util.Optional<hydra.langs.java.syntax.Expression> cond, hydra.langs.java.syntax.StatementNoShortIf body) {
    this.cond = cond;
    this.body = body;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof WhileStatementNoShortIf)) {
      return false;
    }
    WhileStatementNoShortIf o = (WhileStatementNoShortIf) (other);
    return cond.equals(o.cond) && body.equals(o.body);
  }
  
  @Override
  public int hashCode() {
    return 2 * cond.hashCode() + 3 * body.hashCode();
  }
  
  public WhileStatementNoShortIf withCond(java.util.Optional<hydra.langs.java.syntax.Expression> cond) {
    return new WhileStatementNoShortIf(cond, body);
  }
  
  public WhileStatementNoShortIf withBody(hydra.langs.java.syntax.StatementNoShortIf body) {
    return new WhileStatementNoShortIf(cond, body);
  }
}