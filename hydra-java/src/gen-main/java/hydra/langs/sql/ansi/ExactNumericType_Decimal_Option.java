package hydra.langs.sql.ansi;

import java.io.Serializable;

public class ExactNumericType_Decimal_Option implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.ExactNumericType.Decimal.Option");
  
  public final hydra.langs.sql.ansi.Precision precision;
  
  public final java.util.Optional<hydra.langs.sql.ansi.Scale> sequence;
  
  public ExactNumericType_Decimal_Option (hydra.langs.sql.ansi.Precision precision, java.util.Optional<hydra.langs.sql.ansi.Scale> sequence) {
    this.precision = precision;
    this.sequence = sequence;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ExactNumericType_Decimal_Option)) {
      return false;
    }
    ExactNumericType_Decimal_Option o = (ExactNumericType_Decimal_Option) (other);
    return precision.equals(o.precision) && sequence.equals(o.sequence);
  }
  
  @Override
  public int hashCode() {
    return 2 * precision.hashCode() + 3 * sequence.hashCode();
  }
  
  public ExactNumericType_Decimal_Option withPrecision(hydra.langs.sql.ansi.Precision precision) {
    return new ExactNumericType_Decimal_Option(precision, sequence);
  }
  
  public ExactNumericType_Decimal_Option withSequence(java.util.Optional<hydra.langs.sql.ansi.Scale> sequence) {
    return new ExactNumericType_Decimal_Option(precision, sequence);
  }
}