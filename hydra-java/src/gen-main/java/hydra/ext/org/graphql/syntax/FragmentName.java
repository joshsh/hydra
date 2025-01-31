// Note: this is an automatically generated file. Do not edit.

package hydra.ext.graphql.syntax;

import java.io.Serializable;

public class FragmentName implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/ext/graphql/syntax.FragmentName");
  
  public static final hydra.core.Name FIELD_NAME_VALUE = new hydra.core.Name("value");
  
  public final hydra.ext.graphql.syntax.Name value;
  
  public FragmentName (hydra.ext.graphql.syntax.Name value) {
    java.util.Objects.requireNonNull((value));
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
