package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class FieldsDefinition implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.FieldsDefinition");
  
  public final java.util.List<hydra.langs.graphql.syntax.FieldDefinition> value;
  
  public FieldsDefinition (java.util.List<hydra.langs.graphql.syntax.FieldDefinition> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof FieldsDefinition)) {
      return false;
    }
    FieldsDefinition o = (FieldsDefinition) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}