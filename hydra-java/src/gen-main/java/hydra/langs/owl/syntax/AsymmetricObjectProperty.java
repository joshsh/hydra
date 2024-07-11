// Note: this is an automatically generated file. Do not edit.

package hydra.langs.owl.syntax;

import java.io.Serializable;

public class AsymmetricObjectProperty implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.AsymmetricObjectProperty");
  
  public final java.util.List<hydra.langs.owl.syntax.Annotation> annotations;
  
  public final hydra.langs.owl.syntax.ObjectPropertyExpression property;
  
  public AsymmetricObjectProperty (java.util.List<hydra.langs.owl.syntax.Annotation> annotations, hydra.langs.owl.syntax.ObjectPropertyExpression property) {
    java.util.Objects.requireNonNull((annotations));
    java.util.Objects.requireNonNull((property));
    this.annotations = annotations;
    this.property = property;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof AsymmetricObjectProperty)) {
      return false;
    }
    AsymmetricObjectProperty o = (AsymmetricObjectProperty) (other);
    return annotations.equals(o.annotations) && property.equals(o.property);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * property.hashCode();
  }
  
  public AsymmetricObjectProperty withAnnotations(java.util.List<hydra.langs.owl.syntax.Annotation> annotations) {
    java.util.Objects.requireNonNull((annotations));
    return new AsymmetricObjectProperty(annotations, property);
  }
  
  public AsymmetricObjectProperty withProperty(hydra.langs.owl.syntax.ObjectPropertyExpression property) {
    java.util.Objects.requireNonNull((property));
    return new AsymmetricObjectProperty(annotations, property);
  }
}