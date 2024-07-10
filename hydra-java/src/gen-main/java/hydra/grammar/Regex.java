// Note: this is an automatically generated file. Do not edit.

package hydra.grammar;

import java.io.Serializable;

/**
 * A regular expression
 */
public class Regex implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/grammar.Regex");
  
  /**
   * A regular expression
   */
  public final String value;
  
  public Regex (String value) {
    if (value == null) {
      throw new IllegalArgumentException("null value for 'value' argument");
    }
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Regex)) {
      return false;
    }
    Regex o = (Regex) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}