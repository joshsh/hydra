package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class SchemaDefinition implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.SchemaDefinition");
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Description> description;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Directives> directives;
  
  public final hydra.langs.graphql.syntax.RootOperationTypeDefinition rootOperationTypeDefinition;
  
  public SchemaDefinition (java.util.Optional<hydra.langs.graphql.syntax.Description> description, java.util.Optional<hydra.langs.graphql.syntax.Directives> directives, hydra.langs.graphql.syntax.RootOperationTypeDefinition rootOperationTypeDefinition) {
    this.description = description;
    this.directives = directives;
    this.rootOperationTypeDefinition = rootOperationTypeDefinition;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SchemaDefinition)) {
      return false;
    }
    SchemaDefinition o = (SchemaDefinition) (other);
    return description.equals(o.description) && directives.equals(o.directives) && rootOperationTypeDefinition.equals(o.rootOperationTypeDefinition);
  }
  
  @Override
  public int hashCode() {
    return 2 * description.hashCode() + 3 * directives.hashCode() + 5 * rootOperationTypeDefinition.hashCode();
  }
  
  public SchemaDefinition withDescription(java.util.Optional<hydra.langs.graphql.syntax.Description> description) {
    return new SchemaDefinition(description, directives, rootOperationTypeDefinition);
  }
  
  public SchemaDefinition withDirectives(java.util.Optional<hydra.langs.graphql.syntax.Directives> directives) {
    return new SchemaDefinition(description, directives, rootOperationTypeDefinition);
  }
  
  public SchemaDefinition withRootOperationTypeDefinition(hydra.langs.graphql.syntax.RootOperationTypeDefinition rootOperationTypeDefinition) {
    return new SchemaDefinition(description, directives, rootOperationTypeDefinition);
  }
}