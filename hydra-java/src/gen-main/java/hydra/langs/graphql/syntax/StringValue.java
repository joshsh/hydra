package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class StringValue implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.StringValue");
  
  public final String value;
  
  public StringValue (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof StringValue)) {
      return false;
    }
    StringValue o = (StringValue) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}