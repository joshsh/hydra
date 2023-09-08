package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class InterfaceTypeDefinition_Sequence2 implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.InterfaceTypeDefinition.Sequence2");
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Description> description;
  
  public final hydra.langs.graphql.syntax.Name name;
  
  public final hydra.langs.graphql.syntax.ImplementsInterfaces implementsInterfaces;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Directives> directives;
  
  public InterfaceTypeDefinition_Sequence2 (java.util.Optional<hydra.langs.graphql.syntax.Description> description, hydra.langs.graphql.syntax.Name name, hydra.langs.graphql.syntax.ImplementsInterfaces implementsInterfaces, java.util.Optional<hydra.langs.graphql.syntax.Directives> directives) {
    this.description = description;
    this.name = name;
    this.implementsInterfaces = implementsInterfaces;
    this.directives = directives;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof InterfaceTypeDefinition_Sequence2)) {
      return false;
    }
    InterfaceTypeDefinition_Sequence2 o = (InterfaceTypeDefinition_Sequence2) (other);
    return description.equals(o.description) && name.equals(o.name) && implementsInterfaces.equals(o.implementsInterfaces) && directives.equals(o.directives);
  }
  
  @Override
  public int hashCode() {
    return 2 * description.hashCode() + 3 * name.hashCode() + 5 * implementsInterfaces.hashCode() + 7 * directives.hashCode();
  }
  
  public InterfaceTypeDefinition_Sequence2 withDescription(java.util.Optional<hydra.langs.graphql.syntax.Description> description) {
    return new InterfaceTypeDefinition_Sequence2(description, name, implementsInterfaces, directives);
  }
  
  public InterfaceTypeDefinition_Sequence2 withName(hydra.langs.graphql.syntax.Name name) {
    return new InterfaceTypeDefinition_Sequence2(description, name, implementsInterfaces, directives);
  }
  
  public InterfaceTypeDefinition_Sequence2 withImplementsInterfaces(hydra.langs.graphql.syntax.ImplementsInterfaces implementsInterfaces) {
    return new InterfaceTypeDefinition_Sequence2(description, name, implementsInterfaces, directives);
  }
  
  public InterfaceTypeDefinition_Sequence2 withDirectives(java.util.Optional<hydra.langs.graphql.syntax.Directives> directives) {
    return new InterfaceTypeDefinition_Sequence2(description, name, implementsInterfaces, directives);
  }
}