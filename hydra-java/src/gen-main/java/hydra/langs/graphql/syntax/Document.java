package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class Document implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.Document");
  
  public final java.util.List<hydra.langs.graphql.syntax.Definition> value;
  
  public Document (java.util.List<hydra.langs.graphql.syntax.Definition> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Document)) {
      return false;
    }
    Document o = (Document) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}