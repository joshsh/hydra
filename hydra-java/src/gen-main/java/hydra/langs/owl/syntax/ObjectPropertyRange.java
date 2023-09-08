package hydra.langs.owl.syntax;

import java.io.Serializable;

/**
 * See https://www.w3.org/TR/owl2-syntax/#Object_Property_Range
 */
public class ObjectPropertyRange implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.ObjectPropertyRange");
  
  public final java.util.List<hydra.langs.owl.syntax.Annotation> annotations;
  
  public final hydra.langs.owl.syntax.ObjectPropertyExpression property;
  
  public final hydra.langs.owl.syntax.ClassExpression range;
  
  public ObjectPropertyRange (java.util.List<hydra.langs.owl.syntax.Annotation> annotations, hydra.langs.owl.syntax.ObjectPropertyExpression property, hydra.langs.owl.syntax.ClassExpression range) {
    this.annotations = annotations;
    this.property = property;
    this.range = range;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ObjectPropertyRange)) {
      return false;
    }
    ObjectPropertyRange o = (ObjectPropertyRange) (other);
    return annotations.equals(o.annotations) && property.equals(o.property) && range.equals(o.range);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * property.hashCode() + 5 * range.hashCode();
  }
  
  public ObjectPropertyRange withAnnotations(java.util.List<hydra.langs.owl.syntax.Annotation> annotations) {
    return new ObjectPropertyRange(annotations, property, range);
  }
  
  public ObjectPropertyRange withProperty(hydra.langs.owl.syntax.ObjectPropertyExpression property) {
    return new ObjectPropertyRange(annotations, property, range);
  }
  
  public ObjectPropertyRange withRange(hydra.langs.owl.syntax.ClassExpression range) {
    return new ObjectPropertyRange(annotations, property, range);
  }
}