package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_ApplyUnary implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.ApplyUnary");
  
  public final hydra.langs.scala.meta.Data_Name op;
  
  public final hydra.langs.scala.meta.Data arg;
  
  public Data_ApplyUnary (hydra.langs.scala.meta.Data_Name op, hydra.langs.scala.meta.Data arg) {
    this.op = op;
    this.arg = arg;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_ApplyUnary)) {
      return false;
    }
    Data_ApplyUnary o = (Data_ApplyUnary) (other);
    return op.equals(o.op) && arg.equals(o.arg);
  }
  
  @Override
  public int hashCode() {
    return 2 * op.hashCode() + 3 * arg.hashCode();
  }
  
  public Data_ApplyUnary withOp(hydra.langs.scala.meta.Data_Name op) {
    return new Data_ApplyUnary(op, arg);
  }
  
  public Data_ApplyUnary withArg(hydra.langs.scala.meta.Data arg) {
    return new Data_ApplyUnary(op, arg);
  }
}