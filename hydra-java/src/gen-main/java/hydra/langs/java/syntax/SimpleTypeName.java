package hydra.langs.java.syntax;

import java.io.Serializable;

public class SimpleTypeName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.SimpleTypeName");
  
  public final hydra.langs.java.syntax.TypeIdentifier value;
  
  public SimpleTypeName (hydra.langs.java.syntax.TypeIdentifier value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SimpleTypeName)) {
      return false;
    }
    SimpleTypeName o = (SimpleTypeName) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}