package hydra.langs.java.syntax;

import java.io.Serializable;

public class ExpressionName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ExpressionName");
  
  public final java.util.Optional<hydra.langs.java.syntax.AmbiguousName> qualifier;
  
  public final hydra.langs.java.syntax.Identifier identifier;
  
  public ExpressionName (java.util.Optional<hydra.langs.java.syntax.AmbiguousName> qualifier, hydra.langs.java.syntax.Identifier identifier) {
    this.qualifier = qualifier;
    this.identifier = identifier;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ExpressionName)) {
      return false;
    }
    ExpressionName o = (ExpressionName) (other);
    return qualifier.equals(o.qualifier) && identifier.equals(o.identifier);
  }
  
  @Override
  public int hashCode() {
    return 2 * qualifier.hashCode() + 3 * identifier.hashCode();
  }
  
  public ExpressionName withQualifier(java.util.Optional<hydra.langs.java.syntax.AmbiguousName> qualifier) {
    return new ExpressionName(qualifier, identifier);
  }
  
  public ExpressionName withIdentifier(hydra.langs.java.syntax.Identifier identifier) {
    return new ExpressionName(qualifier, identifier);
  }
}