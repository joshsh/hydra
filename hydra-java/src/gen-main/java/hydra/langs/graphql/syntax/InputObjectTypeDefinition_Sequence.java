package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class InputObjectTypeDefinition_Sequence implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.InputObjectTypeDefinition.Sequence");
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Description> description;
  
  public final hydra.langs.graphql.syntax.Name name;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Directives> directives;
  
  public final hydra.langs.graphql.syntax.InputFieldsDefinition inputFieldsDefinition;
  
  public InputObjectTypeDefinition_Sequence (java.util.Optional<hydra.langs.graphql.syntax.Description> description, hydra.langs.graphql.syntax.Name name, java.util.Optional<hydra.langs.graphql.syntax.Directives> directives, hydra.langs.graphql.syntax.InputFieldsDefinition inputFieldsDefinition) {
    this.description = description;
    this.name = name;
    this.directives = directives;
    this.inputFieldsDefinition = inputFieldsDefinition;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof InputObjectTypeDefinition_Sequence)) {
      return false;
    }
    InputObjectTypeDefinition_Sequence o = (InputObjectTypeDefinition_Sequence) (other);
    return description.equals(o.description) && name.equals(o.name) && directives.equals(o.directives) && inputFieldsDefinition.equals(o.inputFieldsDefinition);
  }
  
  @Override
  public int hashCode() {
    return 2 * description.hashCode() + 3 * name.hashCode() + 5 * directives.hashCode() + 7 * inputFieldsDefinition.hashCode();
  }
  
  public InputObjectTypeDefinition_Sequence withDescription(java.util.Optional<hydra.langs.graphql.syntax.Description> description) {
    return new InputObjectTypeDefinition_Sequence(description, name, directives, inputFieldsDefinition);
  }
  
  public InputObjectTypeDefinition_Sequence withName(hydra.langs.graphql.syntax.Name name) {
    return new InputObjectTypeDefinition_Sequence(description, name, directives, inputFieldsDefinition);
  }
  
  public InputObjectTypeDefinition_Sequence withDirectives(java.util.Optional<hydra.langs.graphql.syntax.Directives> directives) {
    return new InputObjectTypeDefinition_Sequence(description, name, directives, inputFieldsDefinition);
  }
  
  public InputObjectTypeDefinition_Sequence withInputFieldsDefinition(hydra.langs.graphql.syntax.InputFieldsDefinition inputFieldsDefinition) {
    return new InputObjectTypeDefinition_Sequence(description, name, directives, inputFieldsDefinition);
  }
}