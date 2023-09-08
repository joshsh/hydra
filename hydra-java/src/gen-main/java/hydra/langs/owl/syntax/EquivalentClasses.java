package hydra.langs.owl.syntax;

import java.io.Serializable;

public class EquivalentClasses implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.EquivalentClasses");
  
  public final java.util.List<hydra.langs.owl.syntax.Annotation> annotations;
  
  public final java.util.List<hydra.langs.owl.syntax.ClassExpression> classes;
  
  public EquivalentClasses (java.util.List<hydra.langs.owl.syntax.Annotation> annotations, java.util.List<hydra.langs.owl.syntax.ClassExpression> classes) {
    this.annotations = annotations;
    this.classes = classes;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EquivalentClasses)) {
      return false;
    }
    EquivalentClasses o = (EquivalentClasses) (other);
    return annotations.equals(o.annotations) && classes.equals(o.classes);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * classes.hashCode();
  }
  
  public EquivalentClasses withAnnotations(java.util.List<hydra.langs.owl.syntax.Annotation> annotations) {
    return new EquivalentClasses(annotations, classes);
  }
  
  public EquivalentClasses withClasses(java.util.List<hydra.langs.owl.syntax.ClassExpression> classes) {
    return new EquivalentClasses(annotations, classes);
  }
}