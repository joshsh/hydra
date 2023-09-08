package hydra.langs.java.syntax;

import java.io.Serializable;

public class SingleElementAnnotation implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.SingleElementAnnotation");
  
  public final hydra.langs.java.syntax.TypeName name;
  
  public final java.util.Optional<hydra.langs.java.syntax.ElementValue> value;
  
  public SingleElementAnnotation (hydra.langs.java.syntax.TypeName name, java.util.Optional<hydra.langs.java.syntax.ElementValue> value) {
    this.name = name;
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SingleElementAnnotation)) {
      return false;
    }
    SingleElementAnnotation o = (SingleElementAnnotation) (other);
    return name.equals(o.name) && value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * value.hashCode();
  }
  
  public SingleElementAnnotation withName(hydra.langs.java.syntax.TypeName name) {
    return new SingleElementAnnotation(name, value);
  }
  
  public SingleElementAnnotation withValue(java.util.Optional<hydra.langs.java.syntax.ElementValue> value) {
    return new SingleElementAnnotation(name, value);
  }
}