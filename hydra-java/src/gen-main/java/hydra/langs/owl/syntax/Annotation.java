package hydra.langs.owl.syntax;

import java.io.Serializable;

public class Annotation implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.Annotation");
  
  public final java.util.List<hydra.langs.owl.syntax.Annotation> annotations;
  
  public final hydra.langs.owl.syntax.AnnotationProperty property;
  
  public final hydra.langs.owl.syntax.AnnotationValue value;
  
  public Annotation (java.util.List<hydra.langs.owl.syntax.Annotation> annotations, hydra.langs.owl.syntax.AnnotationProperty property, hydra.langs.owl.syntax.AnnotationValue value) {
    this.annotations = annotations;
    this.property = property;
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Annotation)) {
      return false;
    }
    Annotation o = (Annotation) (other);
    return annotations.equals(o.annotations) && property.equals(o.property) && value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * property.hashCode() + 5 * value.hashCode();
  }
  
  public Annotation withAnnotations(java.util.List<hydra.langs.owl.syntax.Annotation> annotations) {
    return new Annotation(annotations, property, value);
  }
  
  public Annotation withProperty(hydra.langs.owl.syntax.AnnotationProperty property) {
    return new Annotation(annotations, property, value);
  }
  
  public Annotation withValue(hydra.langs.owl.syntax.AnnotationValue value) {
    return new Annotation(annotations, property, value);
  }
}