// Note: this is an automatically generated file. Do not edit.

package hydra.langs.sql.ansi;

import java.io.Serializable;

public class BooleanFactor implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.BooleanFactor");
  
  public final hydra.util.Opt<java.lang.Void> nOT;
  
  public final hydra.langs.sql.ansi.BooleanTest booleanTest;
  
  public BooleanFactor (hydra.util.Opt<java.lang.Void> nOT, hydra.langs.sql.ansi.BooleanTest booleanTest) {
    if (nOT == null) {
      throw new IllegalArgumentException("null value for 'nOT' argument");
    }
    if (booleanTest == null) {
      throw new IllegalArgumentException("null value for 'booleanTest' argument");
    }
    this.nOT = nOT;
    this.booleanTest = booleanTest;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof BooleanFactor)) {
      return false;
    }
    BooleanFactor o = (BooleanFactor) (other);
    return nOT.equals(o.nOT) && booleanTest.equals(o.booleanTest);
  }
  
  @Override
  public int hashCode() {
    return 2 * nOT.hashCode() + 3 * booleanTest.hashCode();
  }
  
  public BooleanFactor withNOT(hydra.util.Opt<java.lang.Void> nOT) {
    if (nOT == null) {
      throw new IllegalArgumentException("null value for 'nOT' argument");
    }
    return new BooleanFactor(nOT, booleanTest);
  }
  
  public BooleanFactor withBooleanTest(hydra.langs.sql.ansi.BooleanTest booleanTest) {
    if (booleanTest == null) {
      throw new IllegalArgumentException("null value for 'booleanTest' argument");
    }
    return new BooleanFactor(nOT, booleanTest);
  }
}