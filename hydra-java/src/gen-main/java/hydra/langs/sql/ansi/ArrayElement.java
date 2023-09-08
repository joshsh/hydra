package hydra.langs.sql.ansi;

import java.io.Serializable;

public class ArrayElement implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.ArrayElement");
  
  public final hydra.langs.sql.ansi.ValueExpression value;
  
  public ArrayElement (hydra.langs.sql.ansi.ValueExpression value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ArrayElement)) {
      return false;
    }
    ArrayElement o = (ArrayElement) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}