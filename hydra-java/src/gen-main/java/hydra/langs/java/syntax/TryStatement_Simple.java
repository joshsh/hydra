// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class TryStatement_Simple implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.TryStatement.Simple");
  
  public final hydra.langs.java.syntax.Block block;
  
  public final hydra.langs.java.syntax.Catches catches;
  
  public TryStatement_Simple (hydra.langs.java.syntax.Block block, hydra.langs.java.syntax.Catches catches) {
    if (block == null) {
      throw new IllegalArgumentException("null value for 'block' argument");
    }
    if (catches == null) {
      throw new IllegalArgumentException("null value for 'catches' argument");
    }
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
    if (block == null) {
      throw new IllegalArgumentException("null value for 'block' argument");
    }
    return new TryStatement_Simple(block, catches);
  }
  
  public TryStatement_Simple withCatches(hydra.langs.java.syntax.Catches catches) {
    if (catches == null) {
      throw new IllegalArgumentException("null value for 'catches' argument");
    }
    return new TryStatement_Simple(block, catches);
  }
}