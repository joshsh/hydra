package hydra.langs.java.syntax;

import java.io.Serializable;

public class TryWithResourcesStatement implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.TryWithResourcesStatement");
  
  public final hydra.langs.java.syntax.ResourceSpecification resourceSpecification;
  
  public final hydra.langs.java.syntax.Block block;
  
  public final java.util.Optional<hydra.langs.java.syntax.Catches> catches;
  
  public final java.util.Optional<hydra.langs.java.syntax.Finally> finally_;
  
  public TryWithResourcesStatement (hydra.langs.java.syntax.ResourceSpecification resourceSpecification, hydra.langs.java.syntax.Block block, java.util.Optional<hydra.langs.java.syntax.Catches> catches, java.util.Optional<hydra.langs.java.syntax.Finally> finally_) {
    this.resourceSpecification = resourceSpecification;
    this.block = block;
    this.catches = catches;
    this.finally_ = finally_;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TryWithResourcesStatement)) {
      return false;
    }
    TryWithResourcesStatement o = (TryWithResourcesStatement) (other);
    return resourceSpecification.equals(o.resourceSpecification) && block.equals(o.block) && catches.equals(o.catches) && finally_.equals(o.finally_);
  }
  
  @Override
  public int hashCode() {
    return 2 * resourceSpecification.hashCode() + 3 * block.hashCode() + 5 * catches.hashCode() + 7 * finally_.hashCode();
  }
  
  public TryWithResourcesStatement withResourceSpecification(hydra.langs.java.syntax.ResourceSpecification resourceSpecification) {
    return new TryWithResourcesStatement(resourceSpecification, block, catches, finally_);
  }
  
  public TryWithResourcesStatement withBlock(hydra.langs.java.syntax.Block block) {
    return new TryWithResourcesStatement(resourceSpecification, block, catches, finally_);
  }
  
  public TryWithResourcesStatement withCatches(java.util.Optional<hydra.langs.java.syntax.Catches> catches) {
    return new TryWithResourcesStatement(resourceSpecification, block, catches, finally_);
  }
  
  public TryWithResourcesStatement withFinally(java.util.Optional<hydra.langs.java.syntax.Finally> finally_) {
    return new TryWithResourcesStatement(resourceSpecification, block, catches, finally_);
  }
}