// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class LabeledStatement implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/java/syntax.LabeledStatement");
  
  public static final hydra.core.Name FIELD_NAME_IDENTIFIER = new hydra.core.Name("identifier");
  
  public static final hydra.core.Name FIELD_NAME_STATEMENT = new hydra.core.Name("statement");
  
  public final hydra.langs.java.syntax.Identifier identifier;
  
  public final hydra.langs.java.syntax.Statement statement;
  
  public LabeledStatement (hydra.langs.java.syntax.Identifier identifier, hydra.langs.java.syntax.Statement statement) {
    java.util.Objects.requireNonNull((identifier));
    java.util.Objects.requireNonNull((statement));
    this.identifier = identifier;
    this.statement = statement;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof LabeledStatement)) {
      return false;
    }
    LabeledStatement o = (LabeledStatement) (other);
    return identifier.equals(o.identifier) && statement.equals(o.statement);
  }
  
  @Override
  public int hashCode() {
    return 2 * identifier.hashCode() + 3 * statement.hashCode();
  }
  
  public LabeledStatement withIdentifier(hydra.langs.java.syntax.Identifier identifier) {
    java.util.Objects.requireNonNull((identifier));
    return new LabeledStatement(identifier, statement);
  }
  
  public LabeledStatement withStatement(hydra.langs.java.syntax.Statement statement) {
    java.util.Objects.requireNonNull((statement));
    return new LabeledStatement(identifier, statement);
  }
}