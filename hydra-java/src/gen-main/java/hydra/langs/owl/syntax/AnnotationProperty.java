package hydra.langs.owl.syntax;

import java.io.Serializable;

public class AnnotationProperty implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.AnnotationProperty");
  
  public AnnotationProperty () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof AnnotationProperty)) {
      return false;
    }
    AnnotationProperty o = (AnnotationProperty) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}