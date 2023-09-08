package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class DirectiveDefinition implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.DirectiveDefinition");
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Description> description;
  
  public final hydra.langs.graphql.syntax.Name name;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.ArgumentsDefinition> argumentsDefinition;
  
  public final java.util.Optional<java.lang.Void> repeatable;
  
  public final hydra.langs.graphql.syntax.DirectiveLocations directiveLocations;
  
  public DirectiveDefinition (java.util.Optional<hydra.langs.graphql.syntax.Description> description, hydra.langs.graphql.syntax.Name name, java.util.Optional<hydra.langs.graphql.syntax.ArgumentsDefinition> argumentsDefinition, java.util.Optional<java.lang.Void> repeatable, hydra.langs.graphql.syntax.DirectiveLocations directiveLocations) {
    this.description = description;
    this.name = name;
    this.argumentsDefinition = argumentsDefinition;
    this.repeatable = repeatable;
    this.directiveLocations = directiveLocations;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DirectiveDefinition)) {
      return false;
    }
    DirectiveDefinition o = (DirectiveDefinition) (other);
    return description.equals(o.description) && name.equals(o.name) && argumentsDefinition.equals(o.argumentsDefinition) && repeatable.equals(o.repeatable) && directiveLocations.equals(o.directiveLocations);
  }
  
  @Override
  public int hashCode() {
    return 2 * description.hashCode() + 3 * name.hashCode() + 5 * argumentsDefinition.hashCode() + 7 * repeatable.hashCode() + 11 * directiveLocations.hashCode();
  }
  
  public DirectiveDefinition withDescription(java.util.Optional<hydra.langs.graphql.syntax.Description> description) {
    return new DirectiveDefinition(description, name, argumentsDefinition, repeatable, directiveLocations);
  }
  
  public DirectiveDefinition withName(hydra.langs.graphql.syntax.Name name) {
    return new DirectiveDefinition(description, name, argumentsDefinition, repeatable, directiveLocations);
  }
  
  public DirectiveDefinition withArgumentsDefinition(java.util.Optional<hydra.langs.graphql.syntax.ArgumentsDefinition> argumentsDefinition) {
    return new DirectiveDefinition(description, name, argumentsDefinition, repeatable, directiveLocations);
  }
  
  public DirectiveDefinition withRepeatable(java.util.Optional<java.lang.Void> repeatable) {
    return new DirectiveDefinition(description, name, argumentsDefinition, repeatable, directiveLocations);
  }
  
  public DirectiveDefinition withDirectiveLocations(hydra.langs.graphql.syntax.DirectiveLocations directiveLocations) {
    return new DirectiveDefinition(description, name, argumentsDefinition, repeatable, directiveLocations);
  }
}