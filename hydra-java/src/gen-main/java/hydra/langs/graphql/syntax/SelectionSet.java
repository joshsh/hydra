package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class SelectionSet implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.SelectionSet");
  
  public final java.util.List<hydra.langs.graphql.syntax.Selection> value;
  
  public SelectionSet (java.util.List<hydra.langs.graphql.syntax.Selection> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SelectionSet)) {
      return false;
    }
    SelectionSet o = (SelectionSet) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}