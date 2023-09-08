package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class Description implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.Description");
  
  public final hydra.langs.graphql.syntax.StringValue value;
  
  public Description (hydra.langs.graphql.syntax.StringValue value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Description)) {
      return false;
    }
    Description o = (Description) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}