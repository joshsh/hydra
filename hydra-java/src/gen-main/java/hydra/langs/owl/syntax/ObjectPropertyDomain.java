package hydra.langs.owl.syntax;

import java.io.Serializable;

/**
 * See https://www.w3.org/TR/owl2-syntax/#Object_Property_Domain
 */
public class ObjectPropertyDomain implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.ObjectPropertyDomain");
  
  public final java.util.List<hydra.langs.owl.syntax.Annotation> annotations;
  
  public final hydra.langs.owl.syntax.ObjectPropertyExpression property;
  
  public final hydra.langs.owl.syntax.ClassExpression domain;
  
  public ObjectPropertyDomain (java.util.List<hydra.langs.owl.syntax.Annotation> annotations, hydra.langs.owl.syntax.ObjectPropertyExpression property, hydra.langs.owl.syntax.ClassExpression domain) {
    this.annotations = annotations;
    this.property = property;
    this.domain = domain;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ObjectPropertyDomain)) {
      return false;
    }
    ObjectPropertyDomain o = (ObjectPropertyDomain) (other);
    return annotations.equals(o.annotations) && property.equals(o.property) && domain.equals(o.domain);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * property.hashCode() + 5 * domain.hashCode();
  }
  
  public ObjectPropertyDomain withAnnotations(java.util.List<hydra.langs.owl.syntax.Annotation> annotations) {
    return new ObjectPropertyDomain(annotations, property, domain);
  }
  
  public ObjectPropertyDomain withProperty(hydra.langs.owl.syntax.ObjectPropertyExpression property) {
    return new ObjectPropertyDomain(annotations, property, domain);
  }
  
  public ObjectPropertyDomain withDomain(hydra.langs.owl.syntax.ClassExpression domain) {
    return new ObjectPropertyDomain(annotations, property, domain);
  }
}