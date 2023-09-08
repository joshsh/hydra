package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class EnumTypeDefinition implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.EnumTypeDefinition");
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Description> description;
  
  public final hydra.langs.graphql.syntax.Name name;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Directives> directives;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.EnumValuesDefinition> enumValuesDefinition;
  
  public EnumTypeDefinition (java.util.Optional<hydra.langs.graphql.syntax.Description> description, hydra.langs.graphql.syntax.Name name, java.util.Optional<hydra.langs.graphql.syntax.Directives> directives, java.util.Optional<hydra.langs.graphql.syntax.EnumValuesDefinition> enumValuesDefinition) {
    this.description = description;
    this.name = name;
    this.directives = directives;
    this.enumValuesDefinition = enumValuesDefinition;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EnumTypeDefinition)) {
      return false;
    }
    EnumTypeDefinition o = (EnumTypeDefinition) (other);
    return description.equals(o.description) && name.equals(o.name) && directives.equals(o.directives) && enumValuesDefinition.equals(o.enumValuesDefinition);
  }
  
  @Override
  public int hashCode() {
    return 2 * description.hashCode() + 3 * name.hashCode() + 5 * directives.hashCode() + 7 * enumValuesDefinition.hashCode();
  }
  
  public EnumTypeDefinition withDescription(java.util.Optional<hydra.langs.graphql.syntax.Description> description) {
    return new EnumTypeDefinition(description, name, directives, enumValuesDefinition);
  }
  
  public EnumTypeDefinition withName(hydra.langs.graphql.syntax.Name name) {
    return new EnumTypeDefinition(description, name, directives, enumValuesDefinition);
  }
  
  public EnumTypeDefinition withDirectives(java.util.Optional<hydra.langs.graphql.syntax.Directives> directives) {
    return new EnumTypeDefinition(description, name, directives, enumValuesDefinition);
  }
  
  public EnumTypeDefinition withEnumValuesDefinition(java.util.Optional<hydra.langs.graphql.syntax.EnumValuesDefinition> enumValuesDefinition) {
    return new EnumTypeDefinition(description, name, directives, enumValuesDefinition);
  }
}