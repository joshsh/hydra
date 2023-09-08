package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class Argument implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.Argument");
  
  public final hydra.langs.graphql.syntax.Name name;
  
  public final hydra.langs.graphql.syntax.Value value;
  
  public Argument (hydra.langs.graphql.syntax.Name name, hydra.langs.graphql.syntax.Value value) {
    this.name = name;
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Argument)) {
      return false;
    }
    Argument o = (Argument) (other);
    return name.equals(o.name) && value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * value.hashCode();
  }
  
  public Argument withName(hydra.langs.graphql.syntax.Name name) {
    return new Argument(name, value);
  }
  
  public Argument withValue(hydra.langs.graphql.syntax.Value value) {
    return new Argument(name, value);
  }
}