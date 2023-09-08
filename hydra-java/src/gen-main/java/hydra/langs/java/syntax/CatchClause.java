package hydra.langs.java.syntax;

import java.io.Serializable;

public class CatchClause implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.CatchClause");
  
  public final java.util.Optional<hydra.langs.java.syntax.CatchFormalParameter> parameter;
  
  public final hydra.langs.java.syntax.Block block;
  
  public CatchClause (java.util.Optional<hydra.langs.java.syntax.CatchFormalParameter> parameter, hydra.langs.java.syntax.Block block) {
    this.parameter = parameter;
    this.block = block;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof CatchClause)) {
      return false;
    }
    CatchClause o = (CatchClause) (other);
    return parameter.equals(o.parameter) && block.equals(o.block);
  }
  
  @Override
  public int hashCode() {
    return 2 * parameter.hashCode() + 3 * block.hashCode();
  }
  
  public CatchClause withParameter(java.util.Optional<hydra.langs.java.syntax.CatchFormalParameter> parameter) {
    return new CatchClause(parameter, block);
  }
  
  public CatchClause withBlock(hydra.langs.java.syntax.Block block) {
    return new CatchClause(parameter, block);
  }
}