package hydra.langs.java.syntax;

import java.io.Serializable;

public class PrimitiveTypeWithAnnotations implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.PrimitiveTypeWithAnnotations");
  
  public final hydra.langs.java.syntax.PrimitiveType type;
  
  public final java.util.List<hydra.langs.java.syntax.Annotation> annotations;
  
  public PrimitiveTypeWithAnnotations (hydra.langs.java.syntax.PrimitiveType type, java.util.List<hydra.langs.java.syntax.Annotation> annotations) {
    this.type = type;
    this.annotations = annotations;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PrimitiveTypeWithAnnotations)) {
      return false;
    }
    PrimitiveTypeWithAnnotations o = (PrimitiveTypeWithAnnotations) (other);
    return type.equals(o.type) && annotations.equals(o.annotations);
  }
  
  @Override
  public int hashCode() {
    return 2 * type.hashCode() + 3 * annotations.hashCode();
  }
  
  public PrimitiveTypeWithAnnotations withType(hydra.langs.java.syntax.PrimitiveType type) {
    return new PrimitiveTypeWithAnnotations(type, annotations);
  }
  
  public PrimitiveTypeWithAnnotations withAnnotations(java.util.List<hydra.langs.java.syntax.Annotation> annotations) {
    return new PrimitiveTypeWithAnnotations(type, annotations);
  }
}