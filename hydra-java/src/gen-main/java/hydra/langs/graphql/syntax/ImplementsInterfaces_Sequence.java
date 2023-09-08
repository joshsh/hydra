package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class ImplementsInterfaces_Sequence implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.ImplementsInterfaces.Sequence");
  
  public final hydra.langs.graphql.syntax.ImplementsInterfaces implementsInterfaces;
  
  public final hydra.langs.graphql.syntax.NamedType namedType;
  
  public ImplementsInterfaces_Sequence (hydra.langs.graphql.syntax.ImplementsInterfaces implementsInterfaces, hydra.langs.graphql.syntax.NamedType namedType) {
    this.implementsInterfaces = implementsInterfaces;
    this.namedType = namedType;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ImplementsInterfaces_Sequence)) {
      return false;
    }
    ImplementsInterfaces_Sequence o = (ImplementsInterfaces_Sequence) (other);
    return implementsInterfaces.equals(o.implementsInterfaces) && namedType.equals(o.namedType);
  }
  
  @Override
  public int hashCode() {
    return 2 * implementsInterfaces.hashCode() + 3 * namedType.hashCode();
  }
  
  public ImplementsInterfaces_Sequence withImplementsInterfaces(hydra.langs.graphql.syntax.ImplementsInterfaces implementsInterfaces) {
    return new ImplementsInterfaces_Sequence(implementsInterfaces, namedType);
  }
  
  public ImplementsInterfaces_Sequence withNamedType(hydra.langs.graphql.syntax.NamedType namedType) {
    return new ImplementsInterfaces_Sequence(implementsInterfaces, namedType);
  }
}