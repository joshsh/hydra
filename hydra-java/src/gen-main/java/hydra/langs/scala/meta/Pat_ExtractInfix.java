package hydra.langs.scala.meta;

import java.io.Serializable;

public class Pat_ExtractInfix implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Pat.ExtractInfix");
  
  public final hydra.langs.scala.meta.Pat lhs;
  
  public final hydra.langs.scala.meta.Data_Name op;
  
  public final java.util.List<hydra.langs.scala.meta.Pat> rhs;
  
  public Pat_ExtractInfix (hydra.langs.scala.meta.Pat lhs, hydra.langs.scala.meta.Data_Name op, java.util.List<hydra.langs.scala.meta.Pat> rhs) {
    this.lhs = lhs;
    this.op = op;
    this.rhs = rhs;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Pat_ExtractInfix)) {
      return false;
    }
    Pat_ExtractInfix o = (Pat_ExtractInfix) (other);
    return lhs.equals(o.lhs) && op.equals(o.op) && rhs.equals(o.rhs);
  }
  
  @Override
  public int hashCode() {
    return 2 * lhs.hashCode() + 3 * op.hashCode() + 5 * rhs.hashCode();
  }
  
  public Pat_ExtractInfix withLhs(hydra.langs.scala.meta.Pat lhs) {
    return new Pat_ExtractInfix(lhs, op, rhs);
  }
  
  public Pat_ExtractInfix withOp(hydra.langs.scala.meta.Data_Name op) {
    return new Pat_ExtractInfix(lhs, op, rhs);
  }
  
  public Pat_ExtractInfix withRhs(java.util.List<hydra.langs.scala.meta.Pat> rhs) {
    return new Pat_ExtractInfix(lhs, op, rhs);
  }
}