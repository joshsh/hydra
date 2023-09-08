package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class TypeSystemDocment implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.TypeSystemDocment");
  
  public final java.util.List<hydra.langs.graphql.syntax.TypeSystemDefinition> value;
  
  public TypeSystemDocment (java.util.List<hydra.langs.graphql.syntax.TypeSystemDefinition> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TypeSystemDocment)) {
      return false;
    }
    TypeSystemDocment o = (TypeSystemDocment) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}