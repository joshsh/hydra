// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class LabeledStatementNoShortIf implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.LabeledStatementNoShortIf");
  
  public final hydra.langs.java.syntax.Identifier identifier;
  
  public final hydra.langs.java.syntax.StatementNoShortIf statement;
  
  public LabeledStatementNoShortIf (hydra.langs.java.syntax.Identifier identifier, hydra.langs.java.syntax.StatementNoShortIf statement) {
    if (identifier == null) {
      throw new IllegalArgumentException("null value for 'identifier' argument");
    }
    if (statement == null) {
      throw new IllegalArgumentException("null value for 'statement' argument");
    }
    this.identifier = identifier;
    this.statement = statement;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof LabeledStatementNoShortIf)) {
      return false;
    }
    LabeledStatementNoShortIf o = (LabeledStatementNoShortIf) (other);
    return identifier.equals(o.identifier) && statement.equals(o.statement);
  }
  
  @Override
  public int hashCode() {
    return 2 * identifier.hashCode() + 3 * statement.hashCode();
  }
  
  public LabeledStatementNoShortIf withIdentifier(hydra.langs.java.syntax.Identifier identifier) {
    if (identifier == null) {
      throw new IllegalArgumentException("null value for 'identifier' argument");
    }
    return new LabeledStatementNoShortIf(identifier, statement);
  }
  
  public LabeledStatementNoShortIf withStatement(hydra.langs.java.syntax.StatementNoShortIf statement) {
    if (statement == null) {
      throw new IllegalArgumentException("null value for 'statement' argument");
    }
    return new LabeledStatementNoShortIf(identifier, statement);
  }
}