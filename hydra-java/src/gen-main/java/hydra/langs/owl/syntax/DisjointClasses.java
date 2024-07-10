// Note: this is an automatically generated file. Do not edit.

package hydra.langs.owl.syntax;

import java.io.Serializable;

public class DisjointClasses implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.DisjointClasses");
  
  public final java.util.List<hydra.langs.owl.syntax.Annotation> annotations;
  
  public final java.util.List<hydra.langs.owl.syntax.ClassExpression> classes;
  
  public DisjointClasses (java.util.List<hydra.langs.owl.syntax.Annotation> annotations, java.util.List<hydra.langs.owl.syntax.ClassExpression> classes) {
    if (annotations == null) {
      throw new IllegalArgumentException("null value for 'annotations' argument");
    }
    if (classes == null) {
      throw new IllegalArgumentException("null value for 'classes' argument");
    }
    this.annotations = annotations;
    this.classes = classes;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DisjointClasses)) {
      return false;
    }
    DisjointClasses o = (DisjointClasses) (other);
    return annotations.equals(o.annotations) && classes.equals(o.classes);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * classes.hashCode();
  }
  
  public DisjointClasses withAnnotations(java.util.List<hydra.langs.owl.syntax.Annotation> annotations) {
    if (annotations == null) {
      throw new IllegalArgumentException("null value for 'annotations' argument");
    }
    return new DisjointClasses(annotations, classes);
  }
  
  public DisjointClasses withClasses(java.util.List<hydra.langs.owl.syntax.ClassExpression> classes) {
    if (classes == null) {
      throw new IllegalArgumentException("null value for 'classes' argument");
    }
    return new DisjointClasses(annotations, classes);
  }
}