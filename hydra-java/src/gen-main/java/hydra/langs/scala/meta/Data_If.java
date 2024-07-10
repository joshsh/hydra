// Note: this is an automatically generated file. Do not edit.

package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_If implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.If");
  
  public final hydra.langs.scala.meta.Data cond;
  
  public final hydra.langs.scala.meta.Data thenp;
  
  public final hydra.langs.scala.meta.Data elsep;
  
  public Data_If (hydra.langs.scala.meta.Data cond, hydra.langs.scala.meta.Data thenp, hydra.langs.scala.meta.Data elsep) {
    if (cond == null) {
      throw new IllegalArgumentException("null value for 'cond' argument");
    }
    if (thenp == null) {
      throw new IllegalArgumentException("null value for 'thenp' argument");
    }
    if (elsep == null) {
      throw new IllegalArgumentException("null value for 'elsep' argument");
    }
    this.cond = cond;
    this.thenp = thenp;
    this.elsep = elsep;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_If)) {
      return false;
    }
    Data_If o = (Data_If) (other);
    return cond.equals(o.cond) && thenp.equals(o.thenp) && elsep.equals(o.elsep);
  }
  
  @Override
  public int hashCode() {
    return 2 * cond.hashCode() + 3 * thenp.hashCode() + 5 * elsep.hashCode();
  }
  
  public Data_If withCond(hydra.langs.scala.meta.Data cond) {
    if (cond == null) {
      throw new IllegalArgumentException("null value for 'cond' argument");
    }
    return new Data_If(cond, thenp, elsep);
  }
  
  public Data_If withThenp(hydra.langs.scala.meta.Data thenp) {
    if (thenp == null) {
      throw new IllegalArgumentException("null value for 'thenp' argument");
    }
    return new Data_If(cond, thenp, elsep);
  }
  
  public Data_If withElsep(hydra.langs.scala.meta.Data elsep) {
    if (elsep == null) {
      throw new IllegalArgumentException("null value for 'elsep' argument");
    }
    return new Data_If(cond, thenp, elsep);
  }
}