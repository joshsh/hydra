package hydra.langs.owl.syntax;

import java.io.Serializable;

/**
 * See https://www.w3.org/TR/owl2-syntax/#Intersection_of_Data_Ranges
 */
public class DataIntersectionOf implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.DataIntersectionOf");
  
  /**
   * See https://www.w3.org/TR/owl2-syntax/#Intersection_of_Data_Ranges
   */
  public final java.util.List<hydra.langs.owl.syntax.DataRange> value;
  
  public DataIntersectionOf (java.util.List<hydra.langs.owl.syntax.DataRange> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DataIntersectionOf)) {
      return false;
    }
    DataIntersectionOf o = (DataIntersectionOf) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}