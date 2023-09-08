package hydra.langs.sql.ansi;

import java.io.Serializable;

public class ApproximateNumericLiteral implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.ApproximateNumericLiteral");
  
  public final String value;
  
  public ApproximateNumericLiteral (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ApproximateNumericLiteral)) {
      return false;
    }
    ApproximateNumericLiteral o = (ApproximateNumericLiteral) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}