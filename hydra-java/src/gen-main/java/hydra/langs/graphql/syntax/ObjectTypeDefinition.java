package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class ObjectTypeDefinition implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.ObjectTypeDefinition");
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Description> description;
  
  public final hydra.langs.graphql.syntax.Name name;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.ImplementsInterfaces> implementsInterfaces;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Directives> directives;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.FieldsDefinition> fieldsDefinition;
  
  public ObjectTypeDefinition (java.util.Optional<hydra.langs.graphql.syntax.Description> description, hydra.langs.graphql.syntax.Name name, java.util.Optional<hydra.langs.graphql.syntax.ImplementsInterfaces> implementsInterfaces, java.util.Optional<hydra.langs.graphql.syntax.Directives> directives, java.util.Optional<hydra.langs.graphql.syntax.FieldsDefinition> fieldsDefinition) {
    this.description = description;
    this.name = name;
    this.implementsInterfaces = implementsInterfaces;
    this.directives = directives;
    this.fieldsDefinition = fieldsDefinition;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ObjectTypeDefinition)) {
      return false;
    }
    ObjectTypeDefinition o = (ObjectTypeDefinition) (other);
    return description.equals(o.description) && name.equals(o.name) && implementsInterfaces.equals(o.implementsInterfaces) && directives.equals(o.directives) && fieldsDefinition.equals(o.fieldsDefinition);
  }
  
  @Override
  public int hashCode() {
    return 2 * description.hashCode() + 3 * name.hashCode() + 5 * implementsInterfaces.hashCode() + 7 * directives.hashCode() + 11 * fieldsDefinition.hashCode();
  }
  
  public ObjectTypeDefinition withDescription(java.util.Optional<hydra.langs.graphql.syntax.Description> description) {
    return new ObjectTypeDefinition(description, name, implementsInterfaces, directives, fieldsDefinition);
  }
  
  public ObjectTypeDefinition withName(hydra.langs.graphql.syntax.Name name) {
    return new ObjectTypeDefinition(description, name, implementsInterfaces, directives, fieldsDefinition);
  }
  
  public ObjectTypeDefinition withImplementsInterfaces(java.util.Optional<hydra.langs.graphql.syntax.ImplementsInterfaces> implementsInterfaces) {
    return new ObjectTypeDefinition(description, name, implementsInterfaces, directives, fieldsDefinition);
  }
  
  public ObjectTypeDefinition withDirectives(java.util.Optional<hydra.langs.graphql.syntax.Directives> directives) {
    return new ObjectTypeDefinition(description, name, implementsInterfaces, directives, fieldsDefinition);
  }
  
  public ObjectTypeDefinition withFieldsDefinition(java.util.Optional<hydra.langs.graphql.syntax.FieldsDefinition> fieldsDefinition) {
    return new ObjectTypeDefinition(description, name, implementsInterfaces, directives, fieldsDefinition);
  }
}