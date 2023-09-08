package hydra.langs.owl.syntax;

import java.io.Serializable;

public class SubObjectPropertyOf implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.SubObjectPropertyOf");
  
  public final java.util.List<hydra.langs.owl.syntax.Annotation> annotations;
  
  public final java.util.List<hydra.langs.owl.syntax.ObjectPropertyExpression> subProperty;
  
  public final hydra.langs.owl.syntax.ObjectPropertyExpression superProperty;
  
  public SubObjectPropertyOf (java.util.List<hydra.langs.owl.syntax.Annotation> annotations, java.util.List<hydra.langs.owl.syntax.ObjectPropertyExpression> subProperty, hydra.langs.owl.syntax.ObjectPropertyExpression superProperty) {
    this.annotations = annotations;
    this.subProperty = subProperty;
    this.superProperty = superProperty;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SubObjectPropertyOf)) {
      return false;
    }
    SubObjectPropertyOf o = (SubObjectPropertyOf) (other);
    return annotations.equals(o.annotations) && subProperty.equals(o.subProperty) && superProperty.equals(o.superProperty);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * subProperty.hashCode() + 5 * superProperty.hashCode();
  }
  
  public SubObjectPropertyOf withAnnotations(java.util.List<hydra.langs.owl.syntax.Annotation> annotations) {
    return new SubObjectPropertyOf(annotations, subProperty, superProperty);
  }
  
  public SubObjectPropertyOf withSubProperty(java.util.List<hydra.langs.owl.syntax.ObjectPropertyExpression> subProperty) {
    return new SubObjectPropertyOf(annotations, subProperty, superProperty);
  }
  
  public SubObjectPropertyOf withSuperProperty(hydra.langs.owl.syntax.ObjectPropertyExpression superProperty) {
    return new SubObjectPropertyOf(annotations, subProperty, superProperty);
  }
}