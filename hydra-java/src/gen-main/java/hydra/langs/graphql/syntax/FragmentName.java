package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class FragmentName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.FragmentName");
  
  public final hydra.langs.graphql.syntax.Name value;
  
  public FragmentName (hydra.langs.graphql.syntax.Name value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof FragmentName)) {
      return false;
    }
    FragmentName o = (FragmentName) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}