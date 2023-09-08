package hydra.langs.owl.syntax;

import java.io.Serializable;

/**
 * See https://www.w3.org/TR/owl2-syntax/#Union_of_Data_Ranges
 */
public class DataUnionOf implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.DataUnionOf");
  
  /**
   * See https://www.w3.org/TR/owl2-syntax/#Union_of_Data_Ranges
   */
  public final java.util.List<hydra.langs.owl.syntax.DataRange> value;
  
  public DataUnionOf (java.util.List<hydra.langs.owl.syntax.DataRange> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DataUnionOf)) {
      return false;
    }
    DataUnionOf o = (DataUnionOf) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}