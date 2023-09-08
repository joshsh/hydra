package hydra.langs.owl.syntax;

import java.io.Serializable;

/**
 * See https://www.w3.org/TR/owl2-syntax/#Complement_of_Data_Ranges
 */
public class DataComplementOf implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.DataComplementOf");
  
  /**
   * See https://www.w3.org/TR/owl2-syntax/#Complement_of_Data_Ranges
   */
  public final hydra.langs.owl.syntax.DataRange value;
  
  public DataComplementOf (hydra.langs.owl.syntax.DataRange value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DataComplementOf)) {
      return false;
    }
    DataComplementOf o = (DataComplementOf) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}