// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class ClassInstanceCreationExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ClassInstanceCreationExpression");
  
  public final hydra.util.Opt<hydra.langs.java.syntax.ClassInstanceCreationExpression_Qualifier> qualifier;
  
  public final hydra.langs.java.syntax.UnqualifiedClassInstanceCreationExpression expression;
  
  public ClassInstanceCreationExpression (hydra.util.Opt<hydra.langs.java.syntax.ClassInstanceCreationExpression_Qualifier> qualifier, hydra.langs.java.syntax.UnqualifiedClassInstanceCreationExpression expression) {
    if (qualifier == null) {
      throw new IllegalArgumentException("null value for 'qualifier' argument");
    }
    if (expression == null) {
      throw new IllegalArgumentException("null value for 'expression' argument");
    }
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
  
  public ClassInstanceCreationExpression withQualifier(hydra.util.Opt<hydra.langs.java.syntax.ClassInstanceCreationExpression_Qualifier> qualifier) {
    if (qualifier == null) {
      throw new IllegalArgumentException("null value for 'qualifier' argument");
    }
    return new ClassInstanceCreationExpression(qualifier, expression);
  }
  
  public ClassInstanceCreationExpression withExpression(hydra.langs.java.syntax.UnqualifiedClassInstanceCreationExpression expression) {
    if (expression == null) {
      throw new IllegalArgumentException("null value for 'expression' argument");
    }
    return new ClassInstanceCreationExpression(qualifier, expression);
  }
}