package hydra.query;

import java.io.Serializable;

/**
 * A query variable
 */
public class Variable implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/query.Variable");
  
  /**
   * A query variable
   */
  public final String value;
  
  public Variable (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Variable)) {
      return false;
    }
    Variable o = (Variable) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}