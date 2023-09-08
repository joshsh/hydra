package hydra.langs.java.syntax;

import java.io.Serializable;

public class MarkerAnnotation implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.MarkerAnnotation");
  
  public final hydra.langs.java.syntax.TypeName value;
  
  public MarkerAnnotation (hydra.langs.java.syntax.TypeName value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof MarkerAnnotation)) {
      return false;
    }
    MarkerAnnotation o = (MarkerAnnotation) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}