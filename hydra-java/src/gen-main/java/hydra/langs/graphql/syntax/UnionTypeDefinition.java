package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class UnionTypeDefinition implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.UnionTypeDefinition");
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Description> description;
  
  public final hydra.langs.graphql.syntax.Name name;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Directives> directives;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.UnionMemberTypes> unionMemberTypes;
  
  public UnionTypeDefinition (java.util.Optional<hydra.langs.graphql.syntax.Description> description, hydra.langs.graphql.syntax.Name name, java.util.Optional<hydra.langs.graphql.syntax.Directives> directives, java.util.Optional<hydra.langs.graphql.syntax.UnionMemberTypes> unionMemberTypes) {
    this.description = description;
    this.name = name;
    this.directives = directives;
    this.unionMemberTypes = unionMemberTypes;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof UnionTypeDefinition)) {
      return false;
    }
    UnionTypeDefinition o = (UnionTypeDefinition) (other);
    return description.equals(o.description) && name.equals(o.name) && directives.equals(o.directives) && unionMemberTypes.equals(o.unionMemberTypes);
  }
  
  @Override
  public int hashCode() {
    return 2 * description.hashCode() + 3 * name.hashCode() + 5 * directives.hashCode() + 7 * unionMemberTypes.hashCode();
  }
  
  public UnionTypeDefinition withDescription(java.util.Optional<hydra.langs.graphql.syntax.Description> description) {
    return new UnionTypeDefinition(description, name, directives, unionMemberTypes);
  }
  
  public UnionTypeDefinition withName(hydra.langs.graphql.syntax.Name name) {
    return new UnionTypeDefinition(description, name, directives, unionMemberTypes);
  }
  
  public UnionTypeDefinition withDirectives(java.util.Optional<hydra.langs.graphql.syntax.Directives> directives) {
    return new UnionTypeDefinition(description, name, directives, unionMemberTypes);
  }
  
  public UnionTypeDefinition withUnionMemberTypes(java.util.Optional<hydra.langs.graphql.syntax.UnionMemberTypes> unionMemberTypes) {
    return new UnionTypeDefinition(description, name, directives, unionMemberTypes);
  }
}