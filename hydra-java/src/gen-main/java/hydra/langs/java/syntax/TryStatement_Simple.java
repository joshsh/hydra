package hydra.langs.java.syntax;

import java.io.Serializable;

public class TryStatement_Simple implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.TryStatement.Simple");
  
  public final hydra.langs.java.syntax.Block block;
  
  public final hydra.langs.java.syntax.Catches catches;
  
  public TryStatement_Simple (hydra.langs.java.syntax.Block block, hydra.langs.java.syntax.Catches catches) {
    this.block = block;
    this.catches = catches;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TryStatement_Simple)) {
      return false;
    }
    TryStatement_Simple o = (TryStatement_Simple) (other);
    return block.equals(o.block) && catches.equals(o.catches);
  }
  
  @Override
  public int hashCode() {
    return 2 * block.hashCode() + 3 * catches.hashCode();
  }
  
  public TryStatement_Simple withBlock(hydra.langs.java.syntax.Block block) {
    return new TryStatement_Simple(block, catches);
  }
  
  public TryStatement_Simple withCatches(hydra.langs.java.syntax.Catches catches) {
    return new TryStatement_Simple(block, catches);
  }
}