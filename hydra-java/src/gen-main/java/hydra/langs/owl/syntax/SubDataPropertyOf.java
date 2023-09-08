package hydra.langs.owl.syntax;

import java.io.Serializable;

public class SubDataPropertyOf implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.SubDataPropertyOf");
  
  public final java.util.List<hydra.langs.owl.syntax.Annotation> annotations;
  
  public final hydra.langs.owl.syntax.DataPropertyExpression subProperty;
  
  public final hydra.langs.owl.syntax.DataPropertyExpression superProperty;
  
  public SubDataPropertyOf (java.util.List<hydra.langs.owl.syntax.Annotation> annotations, hydra.langs.owl.syntax.DataPropertyExpression subProperty, hydra.langs.owl.syntax.DataPropertyExpression superProperty) {
    this.annotations = annotations;
    this.subProperty = subProperty;
    this.superProperty = superProperty;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SubDataPropertyOf)) {
      return false;
    }
    SubDataPropertyOf o = (SubDataPropertyOf) (other);
    return annotations.equals(o.annotations) && subProperty.equals(o.subProperty) && superProperty.equals(o.superProperty);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * subProperty.hashCode() + 5 * superProperty.hashCode();
  }
  
  public SubDataPropertyOf withAnnotations(java.util.List<hydra.langs.owl.syntax.Annotation> annotations) {
    return new SubDataPropertyOf(annotations, subProperty, superProperty);
  }
  
  public SubDataPropertyOf withSubProperty(hydra.langs.owl.syntax.DataPropertyExpression subProperty) {
    return new SubDataPropertyOf(annotations, subProperty, superProperty);
  }
  
  public SubDataPropertyOf withSuperProperty(hydra.langs.owl.syntax.DataPropertyExpression superProperty) {
    return new SubDataPropertyOf(annotations, subProperty, superProperty);
  }
}