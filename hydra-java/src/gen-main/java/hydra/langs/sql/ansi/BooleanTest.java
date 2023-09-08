package hydra.langs.sql.ansi;

import java.io.Serializable;

public class BooleanTest implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.BooleanTest");
  
  public final hydra.langs.sql.ansi.BooleanPrimary booleanPrimary;
  
  public final java.util.Optional<hydra.langs.sql.ansi.BooleanTest_Sequence_Option> sequence;
  
  public BooleanTest (hydra.langs.sql.ansi.BooleanPrimary booleanPrimary, java.util.Optional<hydra.langs.sql.ansi.BooleanTest_Sequence_Option> sequence) {
    this.booleanPrimary = booleanPrimary;
    this.sequence = sequence;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof BooleanTest)) {
      return false;
    }
    BooleanTest o = (BooleanTest) (other);
    return booleanPrimary.equals(o.booleanPrimary) && sequence.equals(o.sequence);
  }
  
  @Override
  public int hashCode() {
    return 2 * booleanPrimary.hashCode() + 3 * sequence.hashCode();
  }
  
  public BooleanTest withBooleanPrimary(hydra.langs.sql.ansi.BooleanPrimary booleanPrimary) {
    return new BooleanTest(booleanPrimary, sequence);
  }
  
  public BooleanTest withSequence(java.util.Optional<hydra.langs.sql.ansi.BooleanTest_Sequence_Option> sequence) {
    return new BooleanTest(booleanPrimary, sequence);
  }
}