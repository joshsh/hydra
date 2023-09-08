package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class ExecutableDocument implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.ExecutableDocument");
  
  public final java.util.List<hydra.langs.graphql.syntax.ExecutableDefinition> value;
  
  public ExecutableDocument (java.util.List<hydra.langs.graphql.syntax.ExecutableDefinition> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ExecutableDocument)) {
      return false;
    }
    ExecutableDocument o = (ExecutableDocument) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}