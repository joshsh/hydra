package hydra.grammar;

import java.io.Serializable;

/**
 * A constant pattern
 */
public class Constant implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/grammar.Constant");
  
  /**
   * A constant pattern
   */
  public final String value;
  
  public Constant (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Constant)) {
      return false;
    }
    Constant o = (Constant) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}