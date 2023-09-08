package hydra.langs.java.syntax;

import java.io.Serializable;

public class SwitchBlockStatementGroup implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.SwitchBlockStatementGroup");
  
  public final java.util.List<hydra.langs.java.syntax.SwitchLabel> labels;
  
  public final java.util.List<hydra.langs.java.syntax.BlockStatement> statements;
  
  public SwitchBlockStatementGroup (java.util.List<hydra.langs.java.syntax.SwitchLabel> labels, java.util.List<hydra.langs.java.syntax.BlockStatement> statements) {
    this.labels = labels;
    this.statements = statements;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SwitchBlockStatementGroup)) {
      return false;
    }
    SwitchBlockStatementGroup o = (SwitchBlockStatementGroup) (other);
    return labels.equals(o.labels) && statements.equals(o.statements);
  }
  
  @Override
  public int hashCode() {
    return 2 * labels.hashCode() + 3 * statements.hashCode();
  }
  
  public SwitchBlockStatementGroup withLabels(java.util.List<hydra.langs.java.syntax.SwitchLabel> labels) {
    return new SwitchBlockStatementGroup(labels, statements);
  }
  
  public SwitchBlockStatementGroup withStatements(java.util.List<hydra.langs.java.syntax.BlockStatement> statements) {
    return new SwitchBlockStatementGroup(labels, statements);
  }
}