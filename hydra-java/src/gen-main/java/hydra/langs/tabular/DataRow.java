package hydra.langs.tabular;

import java.io.Serializable;

/**
 * A data row, containing untyped cells; one per column
 */
public class DataRow implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tabular.DataRow");
  
  /**
   * A data row, containing untyped cells; one per column
   */
  public final java.util.List<String> value;
  
  public DataRow (java.util.List<String> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DataRow)) {
      return false;
    }
    DataRow o = (DataRow) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}