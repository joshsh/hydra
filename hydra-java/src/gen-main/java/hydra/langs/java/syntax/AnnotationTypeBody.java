package hydra.langs.java.syntax;

import java.io.Serializable;

public class AnnotationTypeBody implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.AnnotationTypeBody");
  
  public final java.util.List<java.util.List<hydra.langs.java.syntax.AnnotationTypeMemberDeclaration>> value;
  
  public AnnotationTypeBody (java.util.List<java.util.List<hydra.langs.java.syntax.AnnotationTypeMemberDeclaration>> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof AnnotationTypeBody)) {
      return false;
    }
    AnnotationTypeBody o = (AnnotationTypeBody) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}