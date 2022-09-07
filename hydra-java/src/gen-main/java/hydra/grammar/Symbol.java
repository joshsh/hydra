package hydra.grammar;

public class Symbol {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/grammar.Symbol");
  
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