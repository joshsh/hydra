package hydra.langs.shex.syntax;

import java.io.Serializable;

public class StartActions implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.StartActions");
  
  public final java.util.List<hydra.langs.shex.syntax.CodeDecl> value;
  
  public StartActions (java.util.List<hydra.langs.shex.syntax.CodeDecl> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof StartActions)) {
      return false;
    }
    StartActions o = (StartActions) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}