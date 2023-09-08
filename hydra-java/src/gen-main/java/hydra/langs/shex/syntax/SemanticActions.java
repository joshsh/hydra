package hydra.langs.shex.syntax;

import java.io.Serializable;

public class SemanticActions implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.SemanticActions");
  
  public final java.util.List<hydra.langs.shex.syntax.CodeDecl> value;
  
  public SemanticActions (java.util.List<hydra.langs.shex.syntax.CodeDecl> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SemanticActions)) {
      return false;
    }
    SemanticActions o = (SemanticActions) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}