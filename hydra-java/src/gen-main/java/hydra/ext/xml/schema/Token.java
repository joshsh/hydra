package hydra.ext.xml.schema;

public class Token {
  public final String value;
  
  public Token (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Token)) {
      return false;
    }
    Token o = (Token) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}