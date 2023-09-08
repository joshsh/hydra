package hydra.langs.java.syntax;

import java.io.Serializable;

public class DoStatement implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.DoStatement");
  
  public final hydra.langs.java.syntax.Statement body;
  
  public final java.util.Optional<hydra.langs.java.syntax.Expression> conde;
  
  public DoStatement (hydra.langs.java.syntax.Statement body, java.util.Optional<hydra.langs.java.syntax.Expression> conde) {
    this.body = body;
    this.conde = conde;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DoStatement)) {
      return false;
    }
    DoStatement o = (DoStatement) (other);
    return body.equals(o.body) && conde.equals(o.conde);
  }
  
  @Override
  public int hashCode() {
    return 2 * body.hashCode() + 3 * conde.hashCode();
  }
  
  public DoStatement withBody(hydra.langs.java.syntax.Statement body) {
    return new DoStatement(body, conde);
  }
  
  public DoStatement withConde(java.util.Optional<hydra.langs.java.syntax.Expression> conde) {
    return new DoStatement(body, conde);
  }
}