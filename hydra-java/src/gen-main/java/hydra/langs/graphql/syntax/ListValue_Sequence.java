package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class ListValue_Sequence implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.ListValue.Sequence");
  
  public ListValue_Sequence () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ListValue_Sequence)) {
      return false;
    }
    ListValue_Sequence o = (ListValue_Sequence) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}