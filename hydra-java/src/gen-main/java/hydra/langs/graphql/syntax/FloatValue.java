package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class FloatValue implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.FloatValue");
  
  public final String value;
  
  public FloatValue (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof FloatValue)) {
      return false;
    }
    FloatValue o = (FloatValue) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}