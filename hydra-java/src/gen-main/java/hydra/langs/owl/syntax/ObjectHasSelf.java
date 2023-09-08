package hydra.langs.owl.syntax;

import java.io.Serializable;

public class ObjectHasSelf implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.ObjectHasSelf");
  
  public final hydra.langs.owl.syntax.ObjectPropertyExpression value;
  
  public ObjectHasSelf (hydra.langs.owl.syntax.ObjectPropertyExpression value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ObjectHasSelf)) {
      return false;
    }
    ObjectHasSelf o = (ObjectHasSelf) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}