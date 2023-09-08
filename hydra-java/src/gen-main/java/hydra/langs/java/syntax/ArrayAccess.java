package hydra.langs.java.syntax;

import java.io.Serializable;

public class ArrayAccess implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ArrayAccess");
  
  public final java.util.Optional<hydra.langs.java.syntax.Expression> expression;
  
  public final hydra.langs.java.syntax.ArrayAccess_Variant variant;
  
  public ArrayAccess (java.util.Optional<hydra.langs.java.syntax.Expression> expression, hydra.langs.java.syntax.ArrayAccess_Variant variant) {
    this.expression = expression;
    this.variant = variant;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ArrayAccess)) {
      return false;
    }
    ArrayAccess o = (ArrayAccess) (other);
    return expression.equals(o.expression) && variant.equals(o.variant);
  }
  
  @Override
  public int hashCode() {
    return 2 * expression.hashCode() + 3 * variant.hashCode();
  }
  
  public ArrayAccess withExpression(java.util.Optional<hydra.langs.java.syntax.Expression> expression) {
    return new ArrayAccess(expression, variant);
  }
  
  public ArrayAccess withVariant(hydra.langs.java.syntax.ArrayAccess_Variant variant) {
    return new ArrayAccess(expression, variant);
  }
}