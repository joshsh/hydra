// Note: this is an automatically generated file. Do not edit.

package hydra.langs.owl.syntax;

import java.io.Serializable;

public class SubDataPropertyOf implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/owl/syntax.SubDataPropertyOf");
  
  public static final hydra.core.Name FIELD_NAME_ANNOTATIONS = new hydra.core.Name("annotations");
  
  public static final hydra.core.Name FIELD_NAME_SUB_PROPERTY = new hydra.core.Name("subProperty");
  
  public static final hydra.core.Name FIELD_NAME_SUPER_PROPERTY = new hydra.core.Name("superProperty");
  
  public final java.util.List<hydra.langs.owl.syntax.Annotation> annotations;
  
  public final hydra.langs.owl.syntax.DataPropertyExpression subProperty;
  
  public final hydra.langs.owl.syntax.DataPropertyExpression superProperty;
  
  public SubDataPropertyOf (java.util.List<hydra.langs.owl.syntax.Annotation> annotations, hydra.langs.owl.syntax.DataPropertyExpression subProperty, hydra.langs.owl.syntax.DataPropertyExpression superProperty) {
    java.util.Objects.requireNonNull((annotations));
    java.util.Objects.requireNonNull((subProperty));
    java.util.Objects.requireNonNull((superProperty));
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
    java.util.Objects.requireNonNull((annotations));
    return new SubDataPropertyOf(annotations, subProperty, superProperty);
  }
  
  public SubDataPropertyOf withSubProperty(hydra.langs.owl.syntax.DataPropertyExpression subProperty) {
    java.util.Objects.requireNonNull((subProperty));
    return new SubDataPropertyOf(annotations, subProperty, superProperty);
  }
  
  public SubDataPropertyOf withSuperProperty(hydra.langs.owl.syntax.DataPropertyExpression superProperty) {
    java.util.Objects.requireNonNull((superProperty));
    return new SubDataPropertyOf(annotations, subProperty, superProperty);
  }
}