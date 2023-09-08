package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class RootOperationTypeDefinition implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.RootOperationTypeDefinition");
  
  public final hydra.langs.graphql.syntax.OperationType operationType;
  
  public final hydra.langs.graphql.syntax.NamedType namedType;
  
  public RootOperationTypeDefinition (hydra.langs.graphql.syntax.OperationType operationType, hydra.langs.graphql.syntax.NamedType namedType) {
    this.operationType = operationType;
    this.namedType = namedType;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof RootOperationTypeDefinition)) {
      return false;
    }
    RootOperationTypeDefinition o = (RootOperationTypeDefinition) (other);
    return operationType.equals(o.operationType) && namedType.equals(o.namedType);
  }
  
  @Override
  public int hashCode() {
    return 2 * operationType.hashCode() + 3 * namedType.hashCode();
  }
  
  public RootOperationTypeDefinition withOperationType(hydra.langs.graphql.syntax.OperationType operationType) {
    return new RootOperationTypeDefinition(operationType, namedType);
  }
  
  public RootOperationTypeDefinition withNamedType(hydra.langs.graphql.syntax.NamedType namedType) {
    return new RootOperationTypeDefinition(operationType, namedType);
  }
}