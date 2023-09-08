package hydra.langs.java.syntax;

import java.io.Serializable;

public class ForUpdate implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ForUpdate");
  
  public final java.util.List<hydra.langs.java.syntax.StatementExpression> value;
  
  public ForUpdate (java.util.List<hydra.langs.java.syntax.StatementExpression> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ForUpdate)) {
      return false;
    }
    ForUpdate o = (ForUpdate) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}