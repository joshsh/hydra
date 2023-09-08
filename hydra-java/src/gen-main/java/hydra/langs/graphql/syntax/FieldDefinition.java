package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class FieldDefinition implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.FieldDefinition");
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Description> description;
  
  public final hydra.langs.graphql.syntax.Name name;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.ArgumentsDefinition> argumentsDefinition;
  
  public final hydra.langs.graphql.syntax.Type type;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Directives> directives;
  
  public FieldDefinition (java.util.Optional<hydra.langs.graphql.syntax.Description> description, hydra.langs.graphql.syntax.Name name, java.util.Optional<hydra.langs.graphql.syntax.ArgumentsDefinition> argumentsDefinition, hydra.langs.graphql.syntax.Type type, java.util.Optional<hydra.langs.graphql.syntax.Directives> directives) {
    this.description = description;
    this.name = name;
    this.argumentsDefinition = argumentsDefinition;
    this.type = type;
    this.directives = directives;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof FieldDefinition)) {
      return false;
    }
    FieldDefinition o = (FieldDefinition) (other);
    return description.equals(o.description) && name.equals(o.name) && argumentsDefinition.equals(o.argumentsDefinition) && type.equals(o.type) && directives.equals(o.directives);
  }
  
  @Override
  public int hashCode() {
    return 2 * description.hashCode() + 3 * name.hashCode() + 5 * argumentsDefinition.hashCode() + 7 * type.hashCode() + 11 * directives.hashCode();
  }
  
  public FieldDefinition withDescription(java.util.Optional<hydra.langs.graphql.syntax.Description> description) {
    return new FieldDefinition(description, name, argumentsDefinition, type, directives);
  }
  
  public FieldDefinition withName(hydra.langs.graphql.syntax.Name name) {
    return new FieldDefinition(description, name, argumentsDefinition, type, directives);
  }
  
  public FieldDefinition withArgumentsDefinition(java.util.Optional<hydra.langs.graphql.syntax.ArgumentsDefinition> argumentsDefinition) {
    return new FieldDefinition(description, name, argumentsDefinition, type, directives);
  }
  
  public FieldDefinition withType(hydra.langs.graphql.syntax.Type type) {
    return new FieldDefinition(description, name, argumentsDefinition, type, directives);
  }
  
  public FieldDefinition withDirectives(java.util.Optional<hydra.langs.graphql.syntax.Directives> directives) {
    return new FieldDefinition(description, name, argumentsDefinition, type, directives);
  }
}