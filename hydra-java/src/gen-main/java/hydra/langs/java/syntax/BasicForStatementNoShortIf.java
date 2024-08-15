// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class BasicForStatementNoShortIf implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/java/syntax.BasicForStatementNoShortIf");
  
  public static final hydra.core.Name FIELD_NAME_COND = new hydra.core.Name("cond");
  
  public static final hydra.core.Name FIELD_NAME_BODY = new hydra.core.Name("body");
  
  public final hydra.langs.java.syntax.ForCond cond;
  
  public final hydra.langs.java.syntax.StatementNoShortIf body;
  
  public BasicForStatementNoShortIf (hydra.langs.java.syntax.ForCond cond, hydra.langs.java.syntax.StatementNoShortIf body) {
    java.util.Objects.requireNonNull((cond));
    java.util.Objects.requireNonNull((body));
    this.cond = cond;
    this.body = body;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof BasicForStatementNoShortIf)) {
      return false;
    }
    BasicForStatementNoShortIf o = (BasicForStatementNoShortIf) (other);
    return cond.equals(o.cond) && body.equals(o.body);
  }
  
  @Override
  public int hashCode() {
    return 2 * cond.hashCode() + 3 * body.hashCode();
  }
  
  public BasicForStatementNoShortIf withCond(hydra.langs.java.syntax.ForCond cond) {
    java.util.Objects.requireNonNull((cond));
    return new BasicForStatementNoShortIf(cond, body);
  }
  
  public BasicForStatementNoShortIf withBody(hydra.langs.java.syntax.StatementNoShortIf body) {
    java.util.Objects.requireNonNull((body));
    return new BasicForStatementNoShortIf(cond, body);
  }
}