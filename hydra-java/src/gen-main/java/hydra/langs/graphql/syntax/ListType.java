package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class ListType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.ListType");
  
  public final hydra.langs.graphql.syntax.Type value;
  
  public ListType (hydra.langs.graphql.syntax.Type value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ListType)) {
      return false;
    }
    ListType o = (ListType) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}