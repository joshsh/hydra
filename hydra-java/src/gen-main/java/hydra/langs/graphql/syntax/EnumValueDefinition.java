package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class EnumValueDefinition implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.EnumValueDefinition");
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Description> description;
  
  public final hydra.langs.graphql.syntax.EnumValue enumValue;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Directives> directives;
  
  public EnumValueDefinition (java.util.Optional<hydra.langs.graphql.syntax.Description> description, hydra.langs.graphql.syntax.EnumValue enumValue, java.util.Optional<hydra.langs.graphql.syntax.Directives> directives) {
    this.description = description;
    this.enumValue = enumValue;
    this.directives = directives;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EnumValueDefinition)) {
      return false;
    }
    EnumValueDefinition o = (EnumValueDefinition) (other);
    return description.equals(o.description) && enumValue.equals(o.enumValue) && directives.equals(o.directives);
  }
  
  @Override
  public int hashCode() {
    return 2 * description.hashCode() + 3 * enumValue.hashCode() + 5 * directives.hashCode();
  }
  
  public EnumValueDefinition withDescription(java.util.Optional<hydra.langs.graphql.syntax.Description> description) {
    return new EnumValueDefinition(description, enumValue, directives);
  }
  
  public EnumValueDefinition withEnumValue(hydra.langs.graphql.syntax.EnumValue enumValue) {
    return new EnumValueDefinition(description, enumValue, directives);
  }
  
  public EnumValueDefinition withDirectives(java.util.Optional<hydra.langs.graphql.syntax.Directives> directives) {
    return new EnumValueDefinition(description, enumValue, directives);
  }
}