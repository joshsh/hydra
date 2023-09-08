package hydra.langs.java.syntax;

import java.io.Serializable;

public class ReturnStatement implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ReturnStatement");
  
  public final java.util.Optional<hydra.langs.java.syntax.Expression> value;
  
  public ReturnStatement (java.util.Optional<hydra.langs.java.syntax.Expression> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ReturnStatement)) {
      return false;
    }
    ReturnStatement o = (ReturnStatement) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}