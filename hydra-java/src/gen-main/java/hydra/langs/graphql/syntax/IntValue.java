package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class IntValue implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.IntValue");
  
  public final String value;
  
  public IntValue (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof IntValue)) {
      return false;
    }
    IntValue o = (IntValue) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}