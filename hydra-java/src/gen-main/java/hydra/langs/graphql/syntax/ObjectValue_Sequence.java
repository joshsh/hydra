package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class ObjectValue_Sequence implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.ObjectValue.Sequence");
  
  public ObjectValue_Sequence () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ObjectValue_Sequence)) {
      return false;
    }
    ObjectValue_Sequence o = (ObjectValue_Sequence) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}