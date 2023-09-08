package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class FragmentSpread implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.FragmentSpread");
  
  public final hydra.langs.graphql.syntax.FragmentName fragmentName;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Directives> directives;
  
  public FragmentSpread (hydra.langs.graphql.syntax.FragmentName fragmentName, java.util.Optional<hydra.langs.graphql.syntax.Directives> directives) {
    this.fragmentName = fragmentName;
    this.directives = directives;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof FragmentSpread)) {
      return false;
    }
    FragmentSpread o = (FragmentSpread) (other);
    return fragmentName.equals(o.fragmentName) && directives.equals(o.directives);
  }
  
  @Override
  public int hashCode() {
    return 2 * fragmentName.hashCode() + 3 * directives.hashCode();
  }
  
  public FragmentSpread withFragmentName(hydra.langs.graphql.syntax.FragmentName fragmentName) {
    return new FragmentSpread(fragmentName, directives);
  }
  
  public FragmentSpread withDirectives(java.util.Optional<hydra.langs.graphql.syntax.Directives> directives) {
    return new FragmentSpread(fragmentName, directives);
  }
}