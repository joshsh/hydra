package hydra.core;

import java.io.Serializable;

/**
 * An object, such as a type or term, together with an annotation
 */
public class Annotated<X, A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/core.Annotated");
  
  public final X subject;
  
  public final A annotation;
  
  public Annotated (X subject, A annotation) {
    this.subject = subject;
    this.annotation = annotation;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Annotated)) {
      return false;
    }
    Annotated o = (Annotated) (other);
    return subject.equals(o.subject) && annotation.equals(o.annotation);
  }
  
  @Override
  public int hashCode() {
    return 2 * subject.hashCode() + 3 * annotation.hashCode();
  }
  
  public Annotated withSubject(X subject) {
    return new Annotated(subject, annotation);
  }
  
  public Annotated withAnnotation(A annotation) {
    return new Annotated(subject, annotation);
  }
}