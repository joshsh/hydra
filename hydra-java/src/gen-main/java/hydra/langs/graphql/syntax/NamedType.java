package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class NamedType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.NamedType");
  
  public final hydra.langs.graphql.syntax.Name value;
  
  public NamedType (hydra.langs.graphql.syntax.Name value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof NamedType)) {
      return false;
    }
    NamedType o = (NamedType) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}