// Note: this is an automatically generated file. Do not edit.

package hydra.langs.sql.ansi;

import java.io.Serializable;

public class ExactNumericType_Dec_Option implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.ExactNumericType.Dec.Option");
  
  public final hydra.langs.sql.ansi.Precision precision;
  
  public final hydra.util.Opt<hydra.langs.sql.ansi.Scale> sequence;
  
  public ExactNumericType_Dec_Option (hydra.langs.sql.ansi.Precision precision, hydra.util.Opt<hydra.langs.sql.ansi.Scale> sequence) {
    java.util.Objects.requireNonNull((precision));
    java.util.Objects.requireNonNull((sequence));
    this.precision = precision;
    this.sequence = sequence;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ExactNumericType_Dec_Option)) {
      return false;
    }
    ExactNumericType_Dec_Option o = (ExactNumericType_Dec_Option) (other);
    return precision.equals(o.precision) && sequence.equals(o.sequence);
  }
  
  @Override
  public int hashCode() {
    return 2 * precision.hashCode() + 3 * sequence.hashCode();
  }
  
  public ExactNumericType_Dec_Option withPrecision(hydra.langs.sql.ansi.Precision precision) {
    java.util.Objects.requireNonNull((precision));
    return new ExactNumericType_Dec_Option(precision, sequence);
  }
  
  public ExactNumericType_Dec_Option withSequence(hydra.util.Opt<hydra.langs.sql.ansi.Scale> sequence) {
    java.util.Objects.requireNonNull((sequence));
    return new ExactNumericType_Dec_Option(precision, sequence);
  }
}