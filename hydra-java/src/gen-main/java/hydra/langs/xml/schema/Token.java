package hydra.langs.xml.schema;

import java.io.Serializable;

public class Token implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/xml/schema.Token");
  
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