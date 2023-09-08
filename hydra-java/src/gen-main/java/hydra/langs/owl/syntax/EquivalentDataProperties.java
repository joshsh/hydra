package hydra.langs.owl.syntax;

import java.io.Serializable;

public class EquivalentDataProperties implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.EquivalentDataProperties");
  
  public final java.util.List<hydra.langs.owl.syntax.Annotation> annotations;
  
  public final java.util.List<hydra.langs.owl.syntax.DataPropertyExpression> properties;
  
  public EquivalentDataProperties (java.util.List<hydra.langs.owl.syntax.Annotation> annotations, java.util.List<hydra.langs.owl.syntax.DataPropertyExpression> properties) {
    this.annotations = annotations;
    this.properties = properties;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EquivalentDataProperties)) {
      return false;
    }
    EquivalentDataProperties o = (EquivalentDataProperties) (other);
    return annotations.equals(o.annotations) && properties.equals(o.properties);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * properties.hashCode();
  }
  
  public EquivalentDataProperties withAnnotations(java.util.List<hydra.langs.owl.syntax.Annotation> annotations) {
    return new EquivalentDataProperties(annotations, properties);
  }
  
  public EquivalentDataProperties withProperties(java.util.List<hydra.langs.owl.syntax.DataPropertyExpression> properties) {
    return new EquivalentDataProperties(annotations, properties);
  }
}