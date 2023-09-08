package hydra.langs.owl.syntax;

import java.io.Serializable;

public class IrreflexiveObjectProperty implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.IrreflexiveObjectProperty");
  
  public final java.util.List<hydra.langs.owl.syntax.Annotation> annotations;
  
  public final hydra.langs.owl.syntax.ObjectPropertyExpression property;
  
  public IrreflexiveObjectProperty (java.util.List<hydra.langs.owl.syntax.Annotation> annotations, hydra.langs.owl.syntax.ObjectPropertyExpression property) {
    this.annotations = annotations;
    this.property = property;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof IrreflexiveObjectProperty)) {
      return false;
    }
    IrreflexiveObjectProperty o = (IrreflexiveObjectProperty) (other);
    return annotations.equals(o.annotations) && property.equals(o.property);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * property.hashCode();
  }
  
  public IrreflexiveObjectProperty withAnnotations(java.util.List<hydra.langs.owl.syntax.Annotation> annotations) {
    return new IrreflexiveObjectProperty(annotations, property);
  }
  
  public IrreflexiveObjectProperty withProperty(hydra.langs.owl.syntax.ObjectPropertyExpression property) {
    return new IrreflexiveObjectProperty(annotations, property);
  }
}