package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class ArgumentsDefinition implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.ArgumentsDefinition");
  
  public final java.util.List<hydra.langs.graphql.syntax.InputValueDefinition> value;
  
  public ArgumentsDefinition (java.util.List<hydra.langs.graphql.syntax.InputValueDefinition> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ArgumentsDefinition)) {
      return false;
    }
    ArgumentsDefinition o = (ArgumentsDefinition) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}