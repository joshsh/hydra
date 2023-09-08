package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class InputObjectTypeExtension_Sequence implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.InputObjectTypeExtension.Sequence");
  
  public final hydra.langs.graphql.syntax.Name name;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Directives> directives;
  
  public final hydra.langs.graphql.syntax.InputFieldsDefinition inputFieldsDefinition;
  
  public InputObjectTypeExtension_Sequence (hydra.langs.graphql.syntax.Name name, java.util.Optional<hydra.langs.graphql.syntax.Directives> directives, hydra.langs.graphql.syntax.InputFieldsDefinition inputFieldsDefinition) {
    this.name = name;
    this.directives = directives;
    this.inputFieldsDefinition = inputFieldsDefinition;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof InputObjectTypeExtension_Sequence)) {
      return false;
    }
    InputObjectTypeExtension_Sequence o = (InputObjectTypeExtension_Sequence) (other);
    return name.equals(o.name) && directives.equals(o.directives) && inputFieldsDefinition.equals(o.inputFieldsDefinition);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * directives.hashCode() + 5 * inputFieldsDefinition.hashCode();
  }
  
  public InputObjectTypeExtension_Sequence withName(hydra.langs.graphql.syntax.Name name) {
    return new InputObjectTypeExtension_Sequence(name, directives, inputFieldsDefinition);
  }
  
  public InputObjectTypeExtension_Sequence withDirectives(java.util.Optional<hydra.langs.graphql.syntax.Directives> directives) {
    return new InputObjectTypeExtension_Sequence(name, directives, inputFieldsDefinition);
  }
  
  public InputObjectTypeExtension_Sequence withInputFieldsDefinition(hydra.langs.graphql.syntax.InputFieldsDefinition inputFieldsDefinition) {
    return new InputObjectTypeExtension_Sequence(name, directives, inputFieldsDefinition);
  }
}