package hydra.langs.owl.syntax;

import java.io.Serializable;

public class ObjectOneOf implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.ObjectOneOf");
  
  public final java.util.List<hydra.langs.owl.syntax.Individual> value;
  
  public ObjectOneOf (java.util.List<hydra.langs.owl.syntax.Individual> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ObjectOneOf)) {
      return false;
    }
    ObjectOneOf o = (ObjectOneOf) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}