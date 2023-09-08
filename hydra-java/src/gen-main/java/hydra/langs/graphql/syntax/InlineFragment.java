package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class InlineFragment implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.InlineFragment");
  
  public final java.util.Optional<hydra.langs.graphql.syntax.TypeCondition> typeCondition;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Directives> directives;
  
  public final hydra.langs.graphql.syntax.SelectionSet selectionSet;
  
  public InlineFragment (java.util.Optional<hydra.langs.graphql.syntax.TypeCondition> typeCondition, java.util.Optional<hydra.langs.graphql.syntax.Directives> directives, hydra.langs.graphql.syntax.SelectionSet selectionSet) {
    this.typeCondition = typeCondition;
    this.directives = directives;
    this.selectionSet = selectionSet;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof InlineFragment)) {
      return false;
    }
    InlineFragment o = (InlineFragment) (other);
    return typeCondition.equals(o.typeCondition) && directives.equals(o.directives) && selectionSet.equals(o.selectionSet);
  }
  
  @Override
  public int hashCode() {
    return 2 * typeCondition.hashCode() + 3 * directives.hashCode() + 5 * selectionSet.hashCode();
  }
  
  public InlineFragment withTypeCondition(java.util.Optional<hydra.langs.graphql.syntax.TypeCondition> typeCondition) {
    return new InlineFragment(typeCondition, directives, selectionSet);
  }
  
  public InlineFragment withDirectives(java.util.Optional<hydra.langs.graphql.syntax.Directives> directives) {
    return new InlineFragment(typeCondition, directives, selectionSet);
  }
  
  public InlineFragment withSelectionSet(hydra.langs.graphql.syntax.SelectionSet selectionSet) {
    return new InlineFragment(typeCondition, directives, selectionSet);
  }
}