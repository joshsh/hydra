package hydra.grammar;

import java.io.Serializable;

/**
 * A nonterminal symbol
 */
public class Symbol implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/grammar.Symbol");
  
  /**
   * A nonterminal symbol
   */
  public final String value;
  
  public Symbol (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Symbol)) {
      return false;
    }
    Symbol o = (Symbol) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}