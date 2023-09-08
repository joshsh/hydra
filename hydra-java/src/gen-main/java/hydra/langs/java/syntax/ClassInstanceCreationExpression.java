package hydra.langs.java.syntax;

import java.io.Serializable;

public class ClassInstanceCreationExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ClassInstanceCreationExpression");
  
  public final java.util.Optional<hydra.langs.java.syntax.ClassInstanceCreationExpression_Qualifier> qualifier;
  
  public final hydra.langs.java.syntax.UnqualifiedClassInstanceCreationExpression expression;
  
  public ClassInstanceCreationExpression (java.util.Optional<hydra.langs.java.syntax.ClassInstanceCreationExpression_Qualifier> qualifier, hydra.langs.java.syntax.UnqualifiedClassInstanceCreationExpression expression) {
    this.qualifier = qualifier;
    this.expression = expression;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ClassInstanceCreationExpression)) {
      return false;
    }
    ClassInstanceCreationExpression o = (ClassInstanceCreationExpression) (other);
    return qualifier.equals(o.qualifier) && expression.equals(o.expression);
  }
  
  @Override
  public int hashCode() {
    return 2 * qualifier.hashCode() + 3 * expression.hashCode();
  }
  
  public ClassInstanceCreationExpression withQualifier(java.util.Optional<hydra.langs.java.syntax.ClassInstanceCreationExpression_Qualifier> qualifier) {
    return new ClassInstanceCreationExpression(qualifier, expression);
  }
  
  public ClassInstanceCreationExpression withExpression(hydra.langs.java.syntax.UnqualifiedClassInstanceCreationExpression expression) {
    return new ClassInstanceCreationExpression(qualifier, expression);
  }
}