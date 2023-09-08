package hydra.langs.owl.syntax;

import java.io.Serializable;

public class AnnotationPropertyRange implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.AnnotationPropertyRange");
  
  public final java.util.List<hydra.langs.owl.syntax.Annotation> annotations;
  
  public final hydra.langs.owl.syntax.AnnotationProperty property;
  
  public final hydra.langs.rdf.syntax.Iri iri;
  
  public AnnotationPropertyRange (java.util.List<hydra.langs.owl.syntax.Annotation> annotations, hydra.langs.owl.syntax.AnnotationProperty property, hydra.langs.rdf.syntax.Iri iri) {
    this.annotations = annotations;
    this.property = property;
    this.iri = iri;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof AnnotationPropertyRange)) {
      return false;
    }
    AnnotationPropertyRange o = (AnnotationPropertyRange) (other);
    return annotations.equals(o.annotations) && property.equals(o.property) && iri.equals(o.iri);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * property.hashCode() + 5 * iri.hashCode();
  }
  
  public AnnotationPropertyRange withAnnotations(java.util.List<hydra.langs.owl.syntax.Annotation> annotations) {
    return new AnnotationPropertyRange(annotations, property, iri);
  }
  
  public AnnotationPropertyRange withProperty(hydra.langs.owl.syntax.AnnotationProperty property) {
    return new AnnotationPropertyRange(annotations, property, iri);
  }
  
  public AnnotationPropertyRange withIri(hydra.langs.rdf.syntax.Iri iri) {
    return new AnnotationPropertyRange(annotations, property, iri);
  }
}