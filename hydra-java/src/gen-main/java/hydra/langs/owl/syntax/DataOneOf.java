package hydra.langs.owl.syntax;

import java.io.Serializable;

/**
 * See https://www.w3.org/TR/owl2-syntax/#Enumeration_of_Literals
 */
public class DataOneOf implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.DataOneOf");
  
  /**
   * See https://www.w3.org/TR/owl2-syntax/#Enumeration_of_Literals
   */
  public final java.util.List<hydra.langs.rdf.syntax.Literal> value;
  
  public DataOneOf (java.util.List<hydra.langs.rdf.syntax.Literal> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DataOneOf)) {
      return false;
    }
    DataOneOf o = (DataOneOf) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}