package hydra.langs.scala.meta;

import java.io.Serializable;

public class Type_ApplyInfix implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Type.ApplyInfix");
  
  public final hydra.langs.scala.meta.Type lhs;
  
  public final hydra.langs.scala.meta.Type_Name op;
  
  public final hydra.langs.scala.meta.Type rhs;
  
  public Type_ApplyInfix (hydra.langs.scala.meta.Type lhs, hydra.langs.scala.meta.Type_Name op, hydra.langs.scala.meta.Type rhs) {
    this.lhs = lhs;
    this.op = op;
    this.rhs = rhs;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Type_ApplyInfix)) {
      return false;
    }
    Type_ApplyInfix o = (Type_ApplyInfix) (other);
    return lhs.equals(o.lhs) && op.equals(o.op) && rhs.equals(o.rhs);
  }
  
  @Override
  public int hashCode() {
    return 2 * lhs.hashCode() + 3 * op.hashCode() + 5 * rhs.hashCode();
  }
  
  public Type_ApplyInfix withLhs(hydra.langs.scala.meta.Type lhs) {
    return new Type_ApplyInfix(lhs, op, rhs);
  }
  
  public Type_ApplyInfix withOp(hydra.langs.scala.meta.Type_Name op) {
    return new Type_ApplyInfix(lhs, op, rhs);
  }
  
  public Type_ApplyInfix withRhs(hydra.langs.scala.meta.Type rhs) {
    return new Type_ApplyInfix(lhs, op, rhs);
  }
}