package hydra.langs.tabular;

import java.io.Serializable;

/**
 * A header row, containing column names (but no types or data)
 */
public class HeaderRow implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tabular.HeaderRow");
  
  /**
   * A header row, containing column names (but no types or data)
   */
  public final java.util.List<String> value;
  
  public HeaderRow (java.util.List<String> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof HeaderRow)) {
      return false;
    }
    HeaderRow o = (HeaderRow) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}