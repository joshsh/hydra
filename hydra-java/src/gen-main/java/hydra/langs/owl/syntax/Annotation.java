// Note: this is an automatically generated file. Do not edit.

package hydra.langs.owl.syntax;

import java.io.Serializable;

public class Annotation implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/owl/syntax.Annotation");
  
  public static final hydra.core.Name FIELD_NAME_ANNOTATIONS = new hydra.core.Name("annotations");
  
  public static final hydra.core.Name FIELD_NAME_PROPERTY = new hydra.core.Name("property");
  
  public static final hydra.core.Name FIELD_NAME_VALUE = new hydra.core.Name("value");
  
  public final java.util.List<hydra.langs.owl.syntax.Annotation> annotations;
  
  public final hydra.langs.owl.syntax.AnnotationProperty property;
  
  public final hydra.langs.owl.syntax.AnnotationValue value;
  
  public Annotation (java.util.List<hydra.langs.owl.syntax.Annotation> annotations, hydra.langs.owl.syntax.AnnotationProperty property, hydra.langs.owl.syntax.AnnotationValue value) {
    java.util.Objects.requireNonNull((annotations));
    java.util.Objects.requireNonNull((property));
    java.util.Objects.requireNonNull((value));
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
    java.util.Objects.requireNonNull((annotations));
    return new Annotation(annotations, property, value);
  }
  
  public Annotation withProperty(hydra.langs.owl.syntax.AnnotationProperty property) {
    java.util.Objects.requireNonNull((property));
    return new Annotation(annotations, property, value);
  }
  
  public Annotation withValue(hydra.langs.owl.syntax.AnnotationValue value) {
    java.util.Objects.requireNonNull((value));
    return new Annotation(annotations, property, value);
  }
}