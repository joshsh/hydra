package hydra.langs.owl.syntax;

import java.io.Serializable;

public class ObjectIntersectionOf implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.ObjectIntersectionOf");
  
  public final java.util.List<hydra.langs.owl.syntax.ClassExpression> value;
  
  public ObjectIntersectionOf (java.util.List<hydra.langs.owl.syntax.ClassExpression> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ObjectIntersectionOf)) {
      return false;
    }
    ObjectIntersectionOf o = (ObjectIntersectionOf) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}