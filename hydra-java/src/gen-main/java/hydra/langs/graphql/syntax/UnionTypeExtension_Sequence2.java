package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class UnionTypeExtension_Sequence2 implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.UnionTypeExtension.Sequence2");
  
  public final hydra.langs.graphql.syntax.Name name;
  
  public final hydra.langs.graphql.syntax.Directives directives;
  
  public UnionTypeExtension_Sequence2 (hydra.langs.graphql.syntax.Name name, hydra.langs.graphql.syntax.Directives directives) {
    this.name = name;
    this.directives = directives;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof UnionTypeExtension_Sequence2)) {
      return false;
    }
    UnionTypeExtension_Sequence2 o = (UnionTypeExtension_Sequence2) (other);
    return name.equals(o.name) && directives.equals(o.directives);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * directives.hashCode();
  }
  
  public UnionTypeExtension_Sequence2 withName(hydra.langs.graphql.syntax.Name name) {
    return new UnionTypeExtension_Sequence2(name, directives);
  }
  
  public UnionTypeExtension_Sequence2 withDirectives(hydra.langs.graphql.syntax.Directives directives) {
    return new UnionTypeExtension_Sequence2(name, directives);
  }
}