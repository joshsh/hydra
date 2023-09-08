package hydra.langs.java.syntax;

import java.io.Serializable;

public class AnnotatedIdentifier implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.AnnotatedIdentifier");
  
  public final java.util.List<hydra.langs.java.syntax.Annotation> annotations;
  
  public final hydra.langs.java.syntax.Identifier identifier;
  
  public AnnotatedIdentifier (java.util.List<hydra.langs.java.syntax.Annotation> annotations, hydra.langs.java.syntax.Identifier identifier) {
    this.annotations = annotations;
    this.identifier = identifier;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof AnnotatedIdentifier)) {
      return false;
    }
    AnnotatedIdentifier o = (AnnotatedIdentifier) (other);
    return annotations.equals(o.annotations) && identifier.equals(o.identifier);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * identifier.hashCode();
  }
  
  public AnnotatedIdentifier withAnnotations(java.util.List<hydra.langs.java.syntax.Annotation> annotations) {
    return new AnnotatedIdentifier(annotations, identifier);
  }
  
  public AnnotatedIdentifier withIdentifier(hydra.langs.java.syntax.Identifier identifier) {
    return new AnnotatedIdentifier(annotations, identifier);
  }
}