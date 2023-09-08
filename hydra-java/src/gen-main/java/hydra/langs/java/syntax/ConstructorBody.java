package hydra.langs.java.syntax;

import java.io.Serializable;

public class ConstructorBody implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ConstructorBody");
  
  public final java.util.Optional<hydra.langs.java.syntax.ExplicitConstructorInvocation> invocation;
  
  public final java.util.List<hydra.langs.java.syntax.BlockStatement> statements;
  
  public ConstructorBody (java.util.Optional<hydra.langs.java.syntax.ExplicitConstructorInvocation> invocation, java.util.List<hydra.langs.java.syntax.BlockStatement> statements) {
    this.invocation = invocation;
    this.statements = statements;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ConstructorBody)) {
      return false;
    }
    ConstructorBody o = (ConstructorBody) (other);
    return invocation.equals(o.invocation) && statements.equals(o.statements);
  }
  
  @Override
  public int hashCode() {
    return 2 * invocation.hashCode() + 3 * statements.hashCode();
  }
  
  public ConstructorBody withInvocation(java.util.Optional<hydra.langs.java.syntax.ExplicitConstructorInvocation> invocation) {
    return new ConstructorBody(invocation, statements);
  }
  
  public ConstructorBody withStatements(java.util.List<hydra.langs.java.syntax.BlockStatement> statements) {
    return new ConstructorBody(invocation, statements);
  }
}