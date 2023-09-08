package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class ObjectField implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.ObjectField");
  
  public final hydra.langs.graphql.syntax.Name name;
  
  public final hydra.langs.graphql.syntax.Value value;
  
  public ObjectField (hydra.langs.graphql.syntax.Name name, hydra.langs.graphql.syntax.Value value) {
    this.name = name;
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ObjectField)) {
      return false;
    }
    ObjectField o = (ObjectField) (other);
    return name.equals(o.name) && value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * value.hashCode();
  }
  
  public ObjectField withName(hydra.langs.graphql.syntax.Name name) {
    return new ObjectField(name, value);
  }
  
  public ObjectField withValue(hydra.langs.graphql.syntax.Value value) {
    return new ObjectField(name, value);
  }
}