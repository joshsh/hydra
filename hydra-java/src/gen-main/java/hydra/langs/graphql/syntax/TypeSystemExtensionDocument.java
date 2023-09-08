package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class TypeSystemExtensionDocument implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.TypeSystemExtensionDocument");
  
  public final java.util.List<hydra.langs.graphql.syntax.TypeSystemDefinitionOrExtension> value;
  
  public TypeSystemExtensionDocument (java.util.List<hydra.langs.graphql.syntax.TypeSystemDefinitionOrExtension> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TypeSystemExtensionDocument)) {
      return false;
    }
    TypeSystemExtensionDocument o = (TypeSystemExtensionDocument) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}