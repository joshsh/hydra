package hydra.langs.owl.syntax;

import java.io.Serializable;

public class DataPropertyExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.DataPropertyExpression");
  
  public final hydra.langs.owl.syntax.DataProperty value;
  
  public DataPropertyExpression (hydra.langs.owl.syntax.DataProperty value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DataPropertyExpression)) {
      return false;
    }
    DataPropertyExpression o = (DataPropertyExpression) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}