// Note: this is an automatically generated file. Do not edit.

package hydra.langs.owl.syntax;

import java.io.Serializable;

public class DisjointDataProperties implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.DisjointDataProperties");
  
  public final java.util.List<hydra.langs.owl.syntax.Annotation> annotations;
  
  public final java.util.List<hydra.langs.owl.syntax.DataPropertyExpression> properties;
  
  public DisjointDataProperties (java.util.List<hydra.langs.owl.syntax.Annotation> annotations, java.util.List<hydra.langs.owl.syntax.DataPropertyExpression> properties) {
    java.util.Objects.requireNonNull((annotations));
    java.util.Objects.requireNonNull((properties));
    this.annotations = annotations;
    this.properties = properties;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DisjointDataProperties)) {
      return false;
    }
    DisjointDataProperties o = (DisjointDataProperties) (other);
    return annotations.equals(o.annotations) && properties.equals(o.properties);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * properties.hashCode();
  }
  
  public DisjointDataProperties withAnnotations(java.util.List<hydra.langs.owl.syntax.Annotation> annotations) {
    java.util.Objects.requireNonNull((annotations));
    return new DisjointDataProperties(annotations, properties);
  }
  
  public DisjointDataProperties withProperties(java.util.List<hydra.langs.owl.syntax.DataPropertyExpression> properties) {
    java.util.Objects.requireNonNull((properties));
    return new DisjointDataProperties(annotations, properties);
  }
}