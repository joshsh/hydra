package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class DefaultValue implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.DefaultValue");
  
  public final hydra.langs.graphql.syntax.Value value;
  
  public DefaultValue (hydra.langs.graphql.syntax.Value value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DefaultValue)) {
      return false;
    }
    DefaultValue o = (DefaultValue) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}