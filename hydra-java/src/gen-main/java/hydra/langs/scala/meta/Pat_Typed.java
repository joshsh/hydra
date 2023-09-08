package hydra.langs.scala.meta;

import java.io.Serializable;

public class Pat_Typed implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Pat.Typed");
  
  public final hydra.langs.scala.meta.Pat lhs;
  
  public final hydra.langs.scala.meta.Type rhs;
  
  public Pat_Typed (hydra.langs.scala.meta.Pat lhs, hydra.langs.scala.meta.Type rhs) {
    this.lhs = lhs;
    this.rhs = rhs;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Pat_Typed)) {
      return false;
    }
    Pat_Typed o = (Pat_Typed) (other);
    return lhs.equals(o.lhs) && rhs.equals(o.rhs);
  }
  
  @Override
  public int hashCode() {
    return 2 * lhs.hashCode() + 3 * rhs.hashCode();
  }
  
  public Pat_Typed withLhs(hydra.langs.scala.meta.Pat lhs) {
    return new Pat_Typed(lhs, rhs);
  }
  
  public Pat_Typed withRhs(hydra.langs.scala.meta.Type rhs) {
    return new Pat_Typed(lhs, rhs);
  }
}