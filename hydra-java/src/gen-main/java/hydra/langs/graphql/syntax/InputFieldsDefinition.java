package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class InputFieldsDefinition implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.InputFieldsDefinition");
  
  public final java.util.List<hydra.langs.graphql.syntax.InputValueDefinition> value;
  
  public InputFieldsDefinition (java.util.List<hydra.langs.graphql.syntax.InputValueDefinition> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof InputFieldsDefinition)) {
      return false;
    }
    InputFieldsDefinition o = (InputFieldsDefinition) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}