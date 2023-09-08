package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class Arguments implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.Arguments");
  
  public final java.util.List<hydra.langs.graphql.syntax.Argument> value;
  
  public Arguments (java.util.List<hydra.langs.graphql.syntax.Argument> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Arguments)) {
      return false;
    }
    Arguments o = (Arguments) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}