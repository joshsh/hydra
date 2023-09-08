package hydra.grammar;

import java.io.Serializable;

/**
 * A name for a pattern
 */
public class Label implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/grammar.Label");
  
  /**
   * A name for a pattern
   */
  public final String value;
  
  public Label (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Label)) {
      return false;
    }
    Label o = (Label) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}