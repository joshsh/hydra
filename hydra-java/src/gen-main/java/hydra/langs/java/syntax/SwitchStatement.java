package hydra.langs.java.syntax;

import java.io.Serializable;

public class SwitchStatement implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.SwitchStatement");
  
  public final hydra.langs.java.syntax.Expression cond;
  
  public final hydra.langs.java.syntax.SwitchBlock block;
  
  public SwitchStatement (hydra.langs.java.syntax.Expression cond, hydra.langs.java.syntax.SwitchBlock block) {
    this.cond = cond;
    this.block = block;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SwitchStatement)) {
      return false;
    }
    SwitchStatement o = (SwitchStatement) (other);
    return cond.equals(o.cond) && block.equals(o.block);
  }
  
  @Override
  public int hashCode() {
    return 2 * cond.hashCode() + 3 * block.hashCode();
  }
  
  public SwitchStatement withCond(hydra.langs.java.syntax.Expression cond) {
    return new SwitchStatement(cond, block);
  }
  
  public SwitchStatement withBlock(hydra.langs.java.syntax.SwitchBlock block) {
    return new SwitchStatement(cond, block);
  }
}