package hydra.langs.scala.meta;

import java.io.Serializable;

public class Pat_Alternative implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Pat.Alternative");
  
  public final hydra.langs.scala.meta.Pat lhs;
  
  public final hydra.langs.scala.meta.Pat rhs;
  
  public Pat_Alternative (hydra.langs.scala.meta.Pat lhs, hydra.langs.scala.meta.Pat rhs) {
    this.lhs = lhs;
    this.rhs = rhs;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Pat_Alternative)) {
      return false;
    }
    Pat_Alternative o = (Pat_Alternative) (other);
    return lhs.equals(o.lhs) && rhs.equals(o.rhs);
  }
  
  @Override
  public int hashCode() {
    return 2 * lhs.hashCode() + 3 * rhs.hashCode();
  }
  
  public Pat_Alternative withLhs(hydra.langs.scala.meta.Pat lhs) {
    return new Pat_Alternative(lhs, rhs);
  }
  
  public Pat_Alternative withRhs(hydra.langs.scala.meta.Pat rhs) {
    return new Pat_Alternative(lhs, rhs);
  }
}