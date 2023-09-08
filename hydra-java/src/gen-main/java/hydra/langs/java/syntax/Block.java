package hydra.langs.java.syntax;

import java.io.Serializable;

public class Block implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.Block");
  
  public final java.util.List<hydra.langs.java.syntax.BlockStatement> value;
  
  public Block (java.util.List<hydra.langs.java.syntax.BlockStatement> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Block)) {
      return false;
    }
    Block o = (Block) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}