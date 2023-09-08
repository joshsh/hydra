package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class UnionMemberTypes_Sequence implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.UnionMemberTypes.Sequence");
  
  public final hydra.langs.graphql.syntax.UnionMemberTypes unionMemberTypes;
  
  public final hydra.langs.graphql.syntax.NamedType namedType;
  
  public UnionMemberTypes_Sequence (hydra.langs.graphql.syntax.UnionMemberTypes unionMemberTypes, hydra.langs.graphql.syntax.NamedType namedType) {
    this.unionMemberTypes = unionMemberTypes;
    this.namedType = namedType;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof UnionMemberTypes_Sequence)) {
      return false;
    }
    UnionMemberTypes_Sequence o = (UnionMemberTypes_Sequence) (other);
    return unionMemberTypes.equals(o.unionMemberTypes) && namedType.equals(o.namedType);
  }
  
  @Override
  public int hashCode() {
    return 2 * unionMemberTypes.hashCode() + 3 * namedType.hashCode();
  }
  
  public UnionMemberTypes_Sequence withUnionMemberTypes(hydra.langs.graphql.syntax.UnionMemberTypes unionMemberTypes) {
    return new UnionMemberTypes_Sequence(unionMemberTypes, namedType);
  }
  
  public UnionMemberTypes_Sequence withNamedType(hydra.langs.graphql.syntax.NamedType namedType) {
    return new UnionMemberTypes_Sequence(unionMemberTypes, namedType);
  }
}