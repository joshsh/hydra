// Note: this is an automatically generated file. Do not edit.

package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class InputObjectTypeExtension_Sequence implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.InputObjectTypeExtension.Sequence");
  
  public final hydra.langs.graphql.syntax.Name name;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Directives> directives;
  
  public final hydra.langs.graphql.syntax.InputFieldsDefinition inputFieldsDefinition;
  
  public InputObjectTypeExtension_Sequence (hydra.langs.graphql.syntax.Name name, java.util.Optional<hydra.langs.graphql.syntax.Directives> directives, hydra.langs.graphql.syntax.InputFieldsDefinition inputFieldsDefinition) {
    if (name == null) {
      throw new IllegalArgumentException("null value for 'name' argument");
    }
    if (directives == null) {
      throw new IllegalArgumentException("null value for 'directives' argument");
    }
    if (inputFieldsDefinition == null) {
      throw new IllegalArgumentException("null value for 'inputFieldsDefinition' argument");
    }
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
    if (name == null) {
      throw new IllegalArgumentException("null value for 'name' argument");
    }
    return new InputObjectTypeExtension_Sequence(name, directives, inputFieldsDefinition);
  }
  
  public InputObjectTypeExtension_Sequence withDirectives(java.util.Optional<hydra.langs.graphql.syntax.Directives> directives) {
    if (directives == null) {
      throw new IllegalArgumentException("null value for 'directives' argument");
    }
    return new InputObjectTypeExtension_Sequence(name, directives, inputFieldsDefinition);
  }
  
  public InputObjectTypeExtension_Sequence withInputFieldsDefinition(hydra.langs.graphql.syntax.InputFieldsDefinition inputFieldsDefinition) {
    if (inputFieldsDefinition == null) {
      throw new IllegalArgumentException("null value for 'inputFieldsDefinition' argument");
    }
    return new InputObjectTypeExtension_Sequence(name, directives, inputFieldsDefinition);
  }
}