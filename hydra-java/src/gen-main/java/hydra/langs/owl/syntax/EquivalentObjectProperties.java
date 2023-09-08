package hydra.langs.owl.syntax;

import java.io.Serializable;

public class EquivalentObjectProperties implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.EquivalentObjectProperties");
  
  public final java.util.List<hydra.langs.owl.syntax.Annotation> annotations;
  
  public final java.util.List<hydra.langs.owl.syntax.ObjectPropertyExpression> properties;
  
  public EquivalentObjectProperties (java.util.List<hydra.langs.owl.syntax.Annotation> annotations, java.util.List<hydra.langs.owl.syntax.ObjectPropertyExpression> properties) {
    this.annotations = annotations;
    this.properties = properties;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EquivalentObjectProperties)) {
      return false;
    }
    EquivalentObjectProperties o = (EquivalentObjectProperties) (other);
    return annotations.equals(o.annotations) && properties.equals(o.properties);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * properties.hashCode();
  }
  
  public EquivalentObjectProperties withAnnotations(java.util.List<hydra.langs.owl.syntax.Annotation> annotations) {
    return new EquivalentObjectProperties(annotations, properties);
  }
  
  public EquivalentObjectProperties withProperties(java.util.List<hydra.langs.owl.syntax.ObjectPropertyExpression> properties) {
    return new EquivalentObjectProperties(annotations, properties);
  }
}