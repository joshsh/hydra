package hydra.langs.sql.ansi;

import java.io.Serializable;

public class BooleanTest_Sequence_Option implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.BooleanTest.Sequence.Option");
  
  public final java.util.Optional<java.lang.Void> nOT;
  
  public final hydra.langs.sql.ansi.TruthValue truthValue;
  
  public BooleanTest_Sequence_Option (java.util.Optional<java.lang.Void> nOT, hydra.langs.sql.ansi.TruthValue truthValue) {
    this.nOT = nOT;
    this.truthValue = truthValue;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof BooleanTest_Sequence_Option)) {
      return false;
    }
    BooleanTest_Sequence_Option o = (BooleanTest_Sequence_Option) (other);
    return nOT.equals(o.nOT) && truthValue.equals(o.truthValue);
  }
  
  @Override
  public int hashCode() {
    return 2 * nOT.hashCode() + 3 * truthValue.hashCode();
  }
  
  public BooleanTest_Sequence_Option withNOT(java.util.Optional<java.lang.Void> nOT) {
    return new BooleanTest_Sequence_Option(nOT, truthValue);
  }
  
  public BooleanTest_Sequence_Option withTruthValue(hydra.langs.sql.ansi.TruthValue truthValue) {
    return new BooleanTest_Sequence_Option(nOT, truthValue);
  }
}